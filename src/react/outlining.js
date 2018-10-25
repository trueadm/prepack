/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { Realm } from "../realm.js";
import { DeclarativeEnvironmentRecord, LexicalEnvironment } from "../environment.js";
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import {
  AbstractObjectValue,
  AbstractValue,
  ArrayValue,
  BoundFunctionValue,
  ConcreteValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  NativeFunctionValue,
  NumberValue,
  ObjectValue,
  PrimitiveValue,
  StringValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { Get } from "../methods/index.js";
import {
  getIntrinsicNameFromTemporalValueDeeplyReferencingPropsObject,
  getValueFromFunctionCall,
  isTemporalValueDeeplyReferencingPropsObject,
  valueIsKnownReactAbstraction,
} from "./utils.js";
import { Functions, Properties } from "../singletons.js";
import { cloneDescriptor, PropertyDescriptor } from "../descriptors.js";
import { createOperationDescriptor } from "../utils/generator.js";
import { ValuesDomain } from "../domains/index.js";
import traverse from "@babel/traverse";
import * as t from "@babel/types";

function collectRuntimeValuesFromFunctionValue(
  realm: Realm,
  val: ECMAScriptSourceFunctionValue,
  runtimeValues: Set<Value>,
  possibleDeadCodeValues: Set<Value>,
  effects: Effects
) {
  let bindings = new Set();
  let body = val.$ECMAScriptCode;
  let params = val.$FormalParameters;

  traverse(
    t.file(t.program([t.expressionStatement(t.functionExpression(null, params, body))])),
    FunctionClosureRefVisitor,
    null,
    bindings
  );
  traverse.cache.clear();
  // Find all bindings
  let env = val.$Environment;
  while (env !== null) {
    let envRec = env.environmentRecord;

    if (envRec instanceof DeclarativeEnvironmentRecord) {
      let envBindings = envRec.bindings;

      for (let envBindingName of Object.keys(envBindings)) {
        if (bindings.has(envBindingName)) {
          let binding = envBindings[envBindingName];
          if (binding !== null && binding.value !== undefined) {
            collectRuntimeValuesFromValue(realm, binding.value, runtimeValues, possibleDeadCodeValues, effects);
          }
        }
      }
    }
    env = env.parent;
  }
}

function applyPreviousEffects(realm, previousEffects, f) {
  realm.withEffectsAppliedInGlobalEnv(() => {
    f();
    return null;
  }, previousEffects);
}

function getValueWithPreviousEffectsApplied(realm, previousEffects, f) {
  let effects;
  let value;
  realm.withEffectsAppliedInGlobalEnv(() => {
    effects = realm.evaluateForEffects(
      () => {
        value = f();
        return realm.intrinsics.undefined;
      },
      undefined,
      "createAbstractTemporalValue"
    );
    f();
    return null;
  }, previousEffects);
  realm.applyEffects(effects);
  return value;
}

function applyPostValueConfig(realm: Realm, value: Value, clonedValue: Value): void {
  if (value instanceof ObjectValue && clonedValue instanceof ObjectValue) {
    if (realm.react.reactProps.has(value)) {
      realm.react.reactProps.add(clonedValue);
    }
    if (value.isPartialObject()) {
      clonedValue.makePartial();
    }
    if (value.isSimpleObject()) {
      clonedValue.makeSimple();
    }
    if (value.mightBeFinalObject()) {
      clonedValue.makeFinal();
    }
  }
}

function cloneAndModelObjectPropertyDescriptor(
  realm: Realm,
  object: ObjectValue,
  clonedObject: ObjectValue,
  desc: PropertyDescriptor,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects,
  alreadyCloned: Map<Value, Value>
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, runtimeValueNameMap, effects, alreadyCloned);
    clonedDesc.value = clonedValue;
  } else {
    invariant(false, "// TODO handle get/set in cloneAndModelObjectPropertyDescriptor");
  }
  return clonedDesc;
}

function visitName(path: BabelTraversePath, bindings: Set<string>, name: string, read: boolean, write: boolean): void {
  // Is the name bound to some local identifier? If so, we don't need to do anything
  if (path.scope.hasBinding(name, /*noGlobals*/ true)) return;

  // Otherwise, let's record that there's an unbound identifier
  if (read) bindings.add(name);
  if (write) bindings.add(name);
}

const FunctionClosureRefVisitor = {
  ReferencedIdentifier(path: BabelTraversePath, bindings: Set<string>): void {
    let innerName = path.node.name;
    if (innerName === "arguments") {
      bindings.usesArguments = true;
      return;
    }
    visitName(path, bindings, innerName, true, false);
  },
  "AssignmentExpression|UpdateExpression"(path: BabelTraversePath, bindings: Set<string>): void {
    let doesRead = path.node.operator !== "=";
    for (let name in path.getBindingIdentifiers()) {
      visitName(path, bindings, name, doesRead, true);
    }
  },
};

function getBinding(bindingName: string, originalEnv: LexicalEnvironment): null | Binding {
  let env = originalEnv;

  while (env !== null) {
    let envRec = env.environmentRecord;

    if (envRec instanceof DeclarativeEnvironmentRecord) {
      let envBindings = envRec.bindings;

      if (envBindings[bindingName]) {
        return envBindings[bindingName];
      }
    }
    env = env.parent;
  }
  return null;
}

function cloneAndModelFunctionScopeForBindings(
  realm: Realm,
  scope: LexicalEnvironment,
  bindings: Set<string>,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects
) {
  let env = new LexicalEnvironment(realm);
  let dclRec = new DeclarativeEnvironmentRecord(realm);
  dclRec.creatingOptimizedFunction = scope.environmentRecord.creatingOptimizedFunction;
  dclRec.lexicalEnvironment = env;
  env.environmentRecord = dclRec;
  if (bindings.size > 0) {
    for (let bindingName of bindings) {
      let binding = getBinding(bindingName, scope);
      // If the binding is null then it's in global scope so we don't need to clone
      if (binding !== null && binding.value !== undefined) {
        let clonedBinding = Object.assign({}, binding);
        clonedBinding.environment = dclRec;
        clonedBinding.value = cloneAndModelValue(realm, binding.value, runtimeValueNameMap, effects);
        dclRec.bindings[bindingName] = clonedBinding;
      }
    }
  }
  env.parent = scope.parent;
  return env;
}

function cloneAndModelFunctionValue(
  realm: Realm,
  val: ECMAScriptSourceFunctionValue,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects
): ECMAScriptSourceFunctionValue {
  let bindings = new Set();
  let body = val.$ECMAScriptCode;
  let params = val.$FormalParameters;

  traverse(
    t.file(t.program([t.expressionStatement(t.functionExpression(null, params, body))])),
    FunctionClosureRefVisitor,
    null,
    bindings
  );
  traverse.cache.clear();
  let clonedScope = cloneAndModelFunctionScopeForBindings(
    realm,
    val.$Environment,
    bindings,
    runtimeValueNameMap,
    effects
  );
  let clonedFunction = Functions.FunctionCreate(realm, val.$FunctionKind, params, body, clonedScope, val.$Strict);
  return clonedFunction;
}

function cloneObjectProperties(
  realm: Realm,
  clonedObject: ObjectValue,
  val: ObjectValue,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects,
  alreadyCloned: Map<Value, Value>
): void {
  // TODO do symbols
  for (let [propName, { descriptor }] of val.properties) {
    if (descriptor === undefined) {
      continue;
    }
    // TODO support prototypes and callee
    if (propName === "prototype" || propName === "callee") {
      invariant(false, "TODO support prototype and callee");
    }
    invariant(descriptor instanceof PropertyDescriptor);
    let desc = cloneAndModelObjectPropertyDescriptor(
      realm,
      val,
      clonedObject,
      descriptor,
      runtimeValueNameMap,
      effects,
      alreadyCloned
    );
    Properties.OrdinaryDefineOwnProperty(realm, clonedObject, propName, desc);
  }
  let unknownProperty = val.unknownProperty;
  if (unknownProperty !== undefined) {
    let desc;
    let key;
    if (unknownProperty.descriptor !== undefined) {
      desc = cloneAndModelObjectPropertyDescriptor(
        realm,
        val,
        clonedObject,
        unknownProperty.descriptor,
        runtimeValueNameMap,
        effects
      );
    }
    if (unknownProperty.key !== undefined) {
      key = cloneAndModelValue(realm, unknownProperty.key, runtimeValueNameMap, effects, alreadyCloned);
    }
    clonedObject.unknownProperty = {
      descriptor: desc,
      key,
      object: clonedObject,
    };
  }
  if (val.temporalAlias !== undefined) {
    clonedObject.temporalAlias = cloneAndModelValue(
      realm,
      val.temporalAlias,
      runtimeValueNameMap,
      effects,
      alreadyCloned
    );
  }
}

function cloneAndModelArrayWithNumericWidenedProperty(
  realm: Realm,
  val: ArrayValue,
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
): ArrayValue {
  let intrinsicName;
  if (isTemporalValueDeeplyReferencingPropsObject(realm, val)) {
    intrinsicName = getIntrinsicNameFromTemporalValueDeeplyReferencingPropsObject(realm, val);
    if (realm.react.outlinedTemporalValue.has(intrinsicName)) {
      let arrayLikeObject = realm.react.outlinedTemporalValue.get(intrinsicName);
      invariant(arrayLikeObject instanceof ArrayValue);
      return arrayLikeObject;
    }
  }
  let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
  invariant(temporalOperationEntry !== undefined);
  let { args, operationDescriptor } = temporalOperationEntry;
  let clonedArgs = args.map(arg => cloneAndModelValue(realm, arg, runtimeValuesMapping, effects));
  if (operationDescriptor.type === "UNKNOWN_ARRAY_METHOD_PROPERTY_CALL") {
    let possibleNestedOptimizedFunctions;
    let [, methodProperty, callbackfn] = clonedArgs;
    invariant(methodProperty instanceof StringValue);
    // For now we only support nested optimized functions on map and filter
    if (methodProperty.value === "map" || methodProperty.value === "filter") {
      possibleNestedOptimizedFunctions = [
        {
          func: callbackfn,
          thisValue: realm.intrinsics.undefined,
          kind: methodProperty.value,
        },
      ];
    }
    let clonedArrayLikeObject = ArrayValue.createTemporalWithWidenedNumericProperty(
      realm,
      clonedArgs,
      createOperationDescriptor("UNKNOWN_ARRAY_METHOD_PROPERTY_CALL"),
      possibleNestedOptimizedFunctions
    );
    if (intrinsicName !== undefined) {
      realm.react.outlinedTemporalValue.set(intrinsicName, clonedArrayLikeObject);
    }
    return clonedArrayLikeObject;
  } else if (operationDescriptor.type === "UNKNOWN_ARRAY_METHOD_CALL") {
    let clonedArrayLikeObject = ArrayValue.createTemporalWithWidenedNumericProperty(
      realm,
      clonedArgs,
      createOperationDescriptor("UNKNOWN_ARRAY_METHOD_CALL")
    );
    if (intrinsicName !== undefined) {
      realm.react.outlinedTemporalValue.set(intrinsicName, clonedArrayLikeObject);
    }
    return clonedArrayLikeObject;
  }
  invariant(false, "TODO");
}

function cloneAndModelObjectValue(
  realm: Realm,
  val: ObjectValue,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects,
  alreadyCloned: Map<Value, Value>
): Value {
  if (!effects.createdObjects.has(val)) {
    return val;
  }
  if (val.isPartialObject() && !realm.react.reactProps.has(val)) {
    invariant(false, "TODO");
  }
  if (val instanceof ArrayValue) {
    if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      return cloneAndModelArrayWithNumericWidenedProperty(realm, val, runtimeValueNameMap, effects, alreadyCloned);
    }
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    alreadyCloned.set(val, clonedObject);
    cloneObjectProperties(realm, clonedObject, val, runtimeValueNameMap, effects, alreadyCloned);
    applyPostValueConfig(realm, val, clonedObject);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    if (val instanceof BoundFunctionValue) {
      invariant(false, "TODO");
    }
    invariant(val instanceof ECMAScriptSourceFunctionValue);
    return cloneAndModelFunctionValue(realm, val, runtimeValueNameMap, effects);
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  alreadyCloned.set(val, clonedObject);
  cloneObjectProperties(realm, clonedObject, val, runtimeValueNameMap, effects, alreadyCloned);
  applyPostValueConfig(realm, val, clonedObject);
  return clonedObject;
}

function cloneAndModelAbstractTemporalValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects,
  alreadyCloned: Map<Value, Value> = new Map()
): AbstractValue {
  let intrinsicName = getIntrinsicNameFromTemporalValueDeeplyReferencingPropsObject(realm, val);
  if (intrinsicName !== undefined && realm.react.outlinedTemporalValue.has(intrinsicName)) {
    let abstractValue = realm.react.outlinedTemporalValue.get(intrinsicName);
    invariant(abstractValue !== undefined);
    return abstractValue;
  }
  let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
  invariant(temporalOperationEntry !== undefined);
  let { args, operationDescriptor } = temporalOperationEntry;
  switch (operationDescriptor.type) {
    case "ABSTRACT_PROPERTY": {
      let clonedTemporalArgs = args.map(arg =>
        cloneAndModelValue(realm, arg, runtimeValueNameMap, effects, alreadyCloned)
      );
      let abstractValue = AbstractValue.createTemporalFromBuildFunction(
        realm,
        val.getType(),
        clonedTemporalArgs,
        createOperationDescriptor("ABSTRACT_PROPERTY"),
        { kind: val.kind, isPure: temporalOperationEntry.isPure, skipInvariant: temporalOperationEntry.skipInvariant }
      );
      realm.react.outlinedTemporalValue.set(intrinsicName, abstractValue);
      return abstractValue;
    }
    case "ABSTRACT_OBJECT_GET": {
      let propertyGetter = operationDescriptor.data.propertyGetter;
      let clonedTemporalArgs = args.map(arg =>
        cloneAndModelValue(realm, arg, runtimeValueNameMap, effects, alreadyCloned)
      );
      let abstractValue = AbstractValue.createTemporalFromBuildFunction(
        realm,
        val.getType(),
        clonedTemporalArgs,
        createOperationDescriptor("ABSTRACT_OBJECT_GET", { propertyGetter }),
        {
          skipInvariant: true,
          isPure: true,
          shape: val.shape,
        }
      );
      realm.react.outlinedTemporalValue.set(intrinsicName, abstractValue);
      return abstractValue;
    }
    case "OBJECT_ASSIGN": {
      let [to, ...sources] = args.map(arg =>
        cloneAndModelValue(realm, arg, runtimeValueNameMap, effects, alreadyCloned)
      );
      let temporalArgs = [to, ...sources];
      let temporalTo = AbstractValue.createTemporalFromBuildFunction(
        realm,
        ObjectValue,
        temporalArgs,
        createOperationDescriptor("OBJECT_ASSIGN"),
        { skipInvariant: true, mutatesOnly: [to] }
      );
      invariant(temporalTo instanceof AbstractObjectValue);
      if (to instanceof AbstractObjectValue) {
        temporalTo.values = to.values;
      } else {
        invariant(to instanceof ObjectValue);
        temporalTo.values = new ValuesDomain(to);
      }
      to.temporalAlias = temporalTo;
      return temporalTo;
    }
    default:
      invariant(false, "TODO");
  }
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects,
  alreadyCloned: Map<Value, Value> = new Map()
): Value {
  if (!effects.createdAbstracts.has(val)) {
    return val;
  }
  if (val.isTemporal()) {
    if (isTemporalValueDeeplyReferencingPropsObject(realm, val)) {
      return cloneAndModelAbstractTemporalValue(realm, val, runtimeValueNameMap, effects, alreadyCloned);
    }
    invariant(false, "Should never get here!");
  } else if (val.kind !== undefined) {
    if (val.kind.startsWith("template:")) {
      let source = val.kind.replace("template:", "");
      let clonedArgs = val.args.map(arg => cloneAndModelValue(realm, arg, runtimeValueNameMap, effects, alreadyCloned));
      return AbstractValue.createFromTemplate(realm, source, val.getType(), clonedArgs);
    } else if (isAbstractValueBinaryExpression(val)) {
      let [leftValue, rightValue] = val.args;
      let clonedLeftValue = cloneAndModelValue(realm, leftValue, runtimeValueNameMap, effects, alreadyCloned);
      let clonedRightValue = cloneAndModelValue(realm, rightValue, runtimeValueNameMap, effects, alreadyCloned);
      return AbstractValue.createFromBinaryOp(realm, val.kind, clonedLeftValue, clonedRightValue);
    } else if (isAbstractValueUnaryExpression(val)) {
      let [condValue] = val.args;
      let clonedCondValue = cloneAndModelValue(realm, condValue, runtimeValueNameMap, effects, alreadyCloned);
      invariant(val.operationDescriptor !== undefined);
      invariant(clonedCondValue instanceof AbstractValue);
      let hasPrefix = val.operationDescriptor.data.prefix;
      return AbstractValue.createFromUnaryOp(realm, val.kind, clonedCondValue, hasPrefix);
    }
    switch (val.kind) {
      case "conditional": {
        let [condValue, consequentVal, alternateVal] = val.args;

        let clonedCondValue = cloneAndModelValue(realm, condValue, runtimeValueNameMap, effects, alreadyCloned);
        let clonedConsequentVal = cloneAndModelValue(realm, consequentVal, runtimeValueNameMap, effects, alreadyCloned);
        let clonedAlternateVal = cloneAndModelValue(realm, alternateVal, runtimeValueNameMap, effects, alreadyCloned);
        return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
      }
      case "||":
      case "&&":
        let [leftValue, rightValue] = val.args;
        let clonedLeftValue = cloneAndModelValue(realm, leftValue, runtimeValueNameMap, effects, alreadyCloned);
        let clonedRightValue = cloneAndModelValue(realm, rightValue, runtimeValueNameMap, effects, alreadyCloned);
        return AbstractValue.createFromLogicalOp(realm, val.kind, clonedLeftValue, clonedRightValue);
        break;
      case "widened numeric property":
        return AbstractValue.createFromType(realm, Value, "widened numeric property", [...val.args]);
      default:
        invariant(false, "TODO");
    }
    invariant(false, "Should not be possible");
  }
}

function cloneAndModelValue(
  realm: Realm,
  val: Value,
  runtimeValueNameMap: Map<Value, string>,
  effects: Effects,
  alreadyCloned?: Map<Value, Value> = new Map()
): Value {
  if (alreadyCloned.has(val)) {
    let clonedVal = alreadyCloned.get(val);
    invariant(clonedVal instanceof Value);
    return clonedVal;
  }
  if (runtimeValueNameMap.has(val)) {
    let runtimeValue = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
    let intrinsicName = runtimeValueNameMap.get(val);
    invariant(intrinsicName !== undefined);
    runtimeValue.intrinsicName = intrinsicName;
    alreadyCloned.set(val, runtimeValue);
    return runtimeValue;
  }
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, runtimeValueNameMap, effects, alreadyCloned);
    }
  } else if (val instanceof AbstractValue) {
    return cloneAndModelAbstractValue(realm, val, runtimeValueNameMap, effects, alreadyCloned);
  }
}

function getValueAndEffectsFromFunctionCall(realm: Realm, func: ECMAScriptSourceFunctionValue, args: Array<Value>) {
  let effects = realm.evaluateForEffects(
    () => {
      if (func instanceof FunctionValue) {
        return getValueFromFunctionCall(realm, func, realm.intrinsics.undefined, args);
      } else {
        return getValueFromFunctionCall(realm, func(), realm.intrinsics.undefined, args);
      }
    },
    null,
    "getValueFromOutlinedFunctionComponent"
  );
  let result = effects.result;
  if (result instanceof AbruptCompletion) {
    invariant(false, "TODO");
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    invariant(false, "TODO");
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  return [effects, result];
}

function setupEnvironmentForOutlining(realm: Realm, collectedRuntimeValues: Set<Value>) {
  realm.react.usedOutlinedValuesArray = true;
  // ensure we define a global value for bindings __rv and __ri in Prepack
  let globalObject = realm.$GlobalObject;
  let __rv = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  globalObject.$DefineOwnProperty(
    "__rv",
    new PropertyDescriptor({
      value: __rv,
      writable: true,
      enumerable: false,
      configurable: true,
    })
  );
  globalObject.$DefineOwnProperty(
    "__ri",
    new PropertyDescriptor({
      value: new NumberValue(realm, 0),
      writable: true,
      enumerable: false,
      configurable: true,
    })
  );
  let globalObj = realm.$GlobalObject;
  globalObject.$DefineOwnProperty(
    "__rd",
    new PropertyDescriptor({
      value: new NativeFunctionValue(realm, undefined, undefined, 0, (context, [id, val]) => {
        let currentIndex = Get(realm, globalObj, "__ri").value;
        collectedRuntimeValues.set(val, { id: id.value, index: currentIndex });
        Properties.Set(realm, globalObj, "__ri", new NumberValue(realm, currentIndex + 1), true);
        return val;
      }),
      writable: true,
      enumerable: false,
      configurable: true,
    })
  );
  globalObject.$DefineOwnProperty(
    "__possibleDeadCode",
    new PropertyDescriptor({
      value: new NativeFunctionValue(realm, undefined, undefined, 0, (context, [val]) => {
        return val;
      }),
      writable: true,
      enumerable: false,
      configurable: true,
    })
  );
}

function shallowCloneFunctionValue(realm: Realm, func: ECMAScriptSourceFunctionValue): ECMAScriptSourceFunctionValue {
  if (realm.react.originalFuncToClonedFunc.has(func)) {
    let clonedFunc = realm.react.originalFuncToClonedFunc.get(func);
    invariant(clonedFunc instanceof ECMAScriptSourceFunctionValue);
    return clonedFunc;
  }
  let body = ((t.cloneDeep(t.blockStatement([func.$ECMAScriptCode])): any): BabelNodeBlockStatement);
  let params = func.$FormalParameters;
  invariant(func.isValid());
  let clonedFunc = Functions.FunctionCreate(realm, func.$FunctionKind, params, body, func.$Environment, func.$Strict);
  realm.react.originalFuncToClonedFunc.set(func, clonedFunc);
  return clonedFunc;
}

function deeplyMakeArgFinal(realm: Realm, arg: Value): void {
  if (arg instanceof ObjectValue) {
    arg.makeFinal();
    for (let [propName, binding] of arg.properties) {
      if (binding && binding.descriptor) {
        let propVal = Get(realm, arg, propName);
        deeplyMakeArgFinal(realm, propVal);
      }
    }
  }
}

function deeplyMakeAllArgsFinal(realm: Realm, args: Array<Value>): void {
  for (let arg of args) {
    deeplyMakeArgFinal(realm, arg);
  }
}

function collectNodes(node, dynamicNodes) {
  if (t.isJSXElement(node)) {
    const openingElement = node.openingElement;

    for (let attr of openingElement.attributes) {
      if (t.isJSXAttribute(attr)) {
        const value = attr.value;
        if (t.isJSXExpressionContainer(value)) {
          dynamicNodes.push(value.expression);
        }
      }
    }
    for (let child of node.children) {
      collectNodes(child, dynamicNodes);
    }
  } else if (t.isJSXExpressionContainer(node)) {
    dynamicNodes.push(node.expression);
  }
}

function createNewNode(path, node) {
  const dynamicNodes = [];
  collectNodes(node, dynamicNodes);
  if (dynamicNodes.length === 0) {
    return t.unaryExpression("void", t.numericLiteral(0));
  }
  return t.sequenceExpression(dynamicNodes);
}

const ReactElementVisitor = {
  JSXElement(path, state) {
    const node = path.node;
    const parentNode = path.parentPath.node;

    if (t.isReturnStatement(parentNode)) {
      let returnParentNode = path.parentPath.parentPath.node;

      for (let returnParentNodeKey of Object.keys(returnParentNode)) {
        let val = returnParentNode[returnParentNodeKey];
        if (val === parentNode) {
          returnParentNode[returnParentNodeKey] = createNewNode(path, node);
          invariant(false, "TODO");
        } else if (Array.isArray(val)) {
          for (let i = 0; i < val.length; i++) {
            if (val[i] === parentNode) {
              val[i] = createNewNode(path, node);
              // Add the return to the line after
              val.splice(i + 1, 0, t.returnStatement());
              return;
            }
          }
        }
      }
    } else if (t.isConditionalExpression(parentNode)) {
      if (parentNode.consequent === node) {
        parentNode.consequent = createNewNode(path, node);
      } else {
        parentNode.alternate = createNewNode(path, node);
      }
    } else if (t.isLogicalExpression(parentNode)) {
      if (parentNode.left === node) {
        parentNode.left = createNewNode(path, node);
      } else {
        parentNode.right = createNewNode(path, node);
      }
    } else if (t.isVariableDeclarator(parentNode)) {
      parentNode.init = createNewNode(path, node);
    } else if (t.isAssignmentExpression(parentNode)) {
      parentNode.right = createNewNode(path, node);
    } else if (t.isCallExpression(parentNode)) {
      let args = parentNode.arguments;
      for (let i = 0; i < args.length; i++) {
        let arg = args[i];
        if (arg === node) {
          args[i] = createNewNode(path, node);
        }
      }
    } else if (t.isSequenceExpression(parentNode)) {
      let expressions = parentNode.expressions;
      for (let i = 0; i < expressions.length; i++) {
        let expression = expressions[i];
        if (expression === node) {
          expressions[i] = createNewNode(path, node);
        }
      }
    }
  },
  CallExpression(path, state) {
    const node = path.node;

    if (t.isIdentifier(node.callee) && node.callee.name === "__possibleDeadCode") {
      const parentNode = path.parentPath.node;

      if (t.isVariableDeclarator(parentNode)) {
        parentNode.init = t.unaryExpression("void", t.numericLiteral(0));
      } else {
        invariant(false, "TODO");
      }
    }
  },
};

export function stripDeadReactCode(realm: Realm): void {
  for (let outlinedFunctionAstNode of realm.react.outlinedFunctionAstNodes) {
    let node = t.isFunctionExpression(outlinedFunctionAstNode)
      ? t.expressionStatement(outlinedFunctionAstNode)
      : outlinedFunctionAstNode;
    traverse(t.file(t.program([node])), ReactElementVisitor, null, null);
  }
  traverse.cache.clear();
}

function isAbstractValueBinaryExpression(val: AbstractValue): boolean {
  const kind = val.kind;
  return (
    val.args.length === 2 &&
    (kind === "!=" ||
      kind === "==" ||
      kind === "==" ||
      kind === "===" ||
      kind === "!==" ||
      kind === "instanceof" ||
      kind === "in" ||
      kind === ">" ||
      kind === "<" ||
      kind === ">=" ||
      kind === "<=" ||
      kind === ">>>" ||
      kind === ">>" ||
      kind === "<<" ||
      kind === "&" ||
      kind === "|" ||
      kind === "^" ||
      kind === "**" ||
      kind === "%" ||
      kind === "/" ||
      kind === "*" ||
      kind === "+" ||
      kind === "-")
  );
}

export function isAbstractValueUnaryExpression(val: AbstractValue): boolean {
  const kind = val.kind;
  return (
    val.args.length === 1 &&
    (kind === "+" ||
      kind === "-" ||
      kind === "!" ||
      kind === "typeof" ||
      kind === "delete" ||
      kind === "void" ||
      kind === "~")
  );
}

function isStaticNode(node) {
  return (
    t.isJSXText(node) ||
    t.isStringLiteral(node) ||
    t.isNumericLiteral(node) ||
    t.isNullLiteral(node) ||
    t.isBooleanLiteral(node)
  );
}

function visitValue(path, node, nodesToWrap, alreadyVisited, scopePaths): void {
  if (alreadyVisited.has(node)) {
    return;
  }
  alreadyVisited.add(node);
  if (isStaticNode(node) || node === null) {
    return;
  }

  if (t.isJSXExpressionContainer(node)) {
    visitValue(path, node.expression, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isCallExpression(node)) {
    nodesToWrap.add(node);
    visitValue(path, node.callee, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isIdentifier(node) || t.isJSXIdentifier(node)) {
    if (path.scope.hasBinding(node.name)) {
      const binding = path.scope.getBinding(node.name);
      const bindingPath = binding.path;
      visitValue(bindingPath, bindingPath.node, nodesToWrap, alreadyVisited, scopePaths);
      for (let referencePath of binding.referencePaths) {
        visitParentNodes(referencePath, referencePath.node, nodesToWrap, alreadyVisited, scopePaths);
      }
    } else {
      nodesToWrap.add(node);
    }
  } else if (
    t.isVariableDeclaration(node) ||
    t.isJSXAttribute(node) ||
    t.isJSXOpeningElement(node) ||
    t.isBlockStatement(node)
  ) {
    // These are both handled in specific locations
    return;
  } else if (t.isVariableDeclarator(node)) {
    visitValue(path, node.id, nodesToWrap, alreadyVisited, scopePaths);
    visitValue(path, node.init, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isObjectExpression(node)) {
    for (let property of node.properties) {
      visitValue(path, property, nodesToWrap, alreadyVisited, scopePaths);
    }
  } else if (t.isObjectProperty(node)) {
    if (node.computed) {
      visitValue(path, node.key, nodesToWrap, alreadyVisited, scopePaths);
    }
    visitValue(path, node.value, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isMemberExpression(node)) {
    nodesToWrap.add(node);
    visitValue(path, node.object, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isArrayExpression(node)) {
    for (let element of node.elements) {
      visitValue(path, element, nodesToWrap, alreadyVisited, scopePaths);
    }
  } else if (t.isConditionalExpression(node)) {
    nodesToWrap.add(node);
    visitValue(path, node.test, nodesToWrap, alreadyVisited, scopePaths);
    visitValue(path, node.consequent, nodesToWrap, alreadyVisited, scopePaths);
    visitValue(path, node.alternate, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isIfStatement(node)) {
    visitValue(path, node.test, nodesToWrap, alreadyVisited);
    visitValue(path, node.consequent, nodesToWrap, alreadyVisited, scopePaths);
    visitValue(path, node.alternate, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isJSXElement(node)) {
    visitReactElement(path, node, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isAssignmentExpression(node)) {
    visitValue(path, node.left, nodesToWrap, alreadyVisited, scopePaths);
    visitValue(path, node.right, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isLogicalExpression(node)) {
    nodesToWrap.add(node);
    visitValue(path, node.left, nodesToWrap, alreadyVisited, scopePaths);
    visitValue(path, node.right, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isBinaryExpression(node)) {
    nodesToWrap.add(node);
    visitValue(path, node.left, nodesToWrap, alreadyVisited, scopePaths);
    visitValue(path, node.right, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isExpressionStatement(node)) {
    visitValue(path, node.expression, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isReturnStatement(node)) {
    visitValue(path, node.argument, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isJSXSpreadAttribute(node)) {
    nodesToWrap.add(node.argument);
    visitValue(path, node.argument, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isUnaryExpression(node)) {
    nodesToWrap.add(node);
    visitValue(path, node.argument, nodesToWrap, alreadyVisited, scopePaths);
  } else if (t.isFunctionDeclaration(node) || t.isFunctionExpression(node) || t.isArrowFunctionExpression(node)) {
    // Ensure we move scope if we're not already in it
    let functionPath = scopePaths.get(node);
    invariant(functionPath !== undefined);
    // Find the return statement
    functionPath.traverse({
      ReturnStatement(returnPath) {
        visitValue(returnPath, returnPath.node, nodesToWrap, alreadyVisited, scopePaths);
      },
    });
  } else {
    debugger;
  }
}

function visitParentNodes(path, node, nodesToWrap, alreadyVisited, scopePaths) {
  let parentPath = path.parentPath;
  while (parentPath !== undefined) {
    let parentNode = parentPath.node;

    if (
      t.isFunctionExpression(parentNode) ||
      t.isArrowFunctionExpression(parentNode) ||
      t.isFunctionDeclaration(parentNode) ||
      t.isBlockStatement(parentNode)
    ) {
      break;
    }
    visitValue(path, parentNode, nodesToWrap, alreadyVisited, scopePaths);
    parentPath = parentPath.parentPath;
  }
}

function visitReactElement(path, node, nodesToWrap, alreadyVisited, scopePaths): void {
  const openingElement = node.openingElement;
  const name = openingElement.name;

  if (t.isJSXIdentifier(name)) {
    const firstChar = name.name[0];
    if (firstChar !== firstChar.toLowerCase() || firstChar === "_" || firstChar === "$") {
      visitValue(path, name, nodesToWrap, alreadyVisited, scopePaths);
    }
  }
  for (let attr of openingElement.attributes) {
    if (t.isJSXAttribute(attr)) {
      const value = attr.value;
      if (t.isJSXExpressionContainer(value)) {
        visitValue(path, value, nodesToWrap, alreadyVisited, scopePaths);
      }
    } else if (t.isJSXSpreadAttribute(attr)) {
      visitValue(path, attr, nodesToWrap, alreadyVisited, scopePaths);
    }
  }
  for (let child of node.children) {
    visitValue(path, child, nodesToWrap, alreadyVisited, scopePaths);
  }
  visitParentNodes(path, node, nodesToWrap, alreadyVisited, scopePaths);
}

const ReactValueVisitor = {
  "FunctionDeclaration|FunctionExpression|ArrowFunctionExpression"(path, { scopePaths }) {
    scopePaths.set(path.node, path);
  },
  CallExpression: {
    exit(path, { nodesToWrap, alreadyVisited, scopePaths }) {
      const node = path.node;
      if (t.isIdentifier(node.callee) && node.callee.name === "__optimizeReactComponentTree") {
        let component = node.arguments[0];
        if (t.isIdentifier(component)) {
          let binding = path.scope.getBinding(component.name);
          invariant(binding !== undefined);
          let bindingPath = binding.path;
          let bindingNode = bindingPath.node;

          invariant(
            t.isFunctionDeclaration(bindingNode) ||
              t.isFunctionExpression(bindingNode) ||
              t.isArrowFunctionExpression(bindingNode)
          );
          visitValue(bindingPath, bindingNode, nodesToWrap, alreadyVisited, scopePaths);
        }
      }
    },
  },
};

// visitReactElement(path, path.node, nodesToWrap, alreadyVisited, blockOrScopeToVisit);

const ReactWrapperVisitor = {
  "LogicalExpression|CallExpression|ConditionalExpression|BinaryExpression|UnaryExpression|Identifier|JSXIdentifier": {
    exit(path, { nodesToWrap, idCounter }) {
      const node = path.node;

      if (nodesToWrap.has(node)) {
        nodesToWrap.delete(node);
        path.replaceWith(
          t.callExpression(t.identifier("__rd"), [t.numericLiteral(idCounter.counter++), t.cloneDeep(node)])
        );
      }
    },
  },
  MemberExpression: {
    exit(path, { nodesToWrap, idCounter }) {
      const node = path.node;
      let parentNode = path.parentPath.node;

      if (nodesToWrap.has(node)) {
        nodesToWrap.delete(node);
        if (t.isMemberExpression(parentNode) || t.isCallExpression(parentNode)) {
          // Skip
          return;
        }
        // Skip assignment replacements on id
        if (t.isAssignmentExpression(parentNode) & (parentNode.left === node)) {
          return;
        }
        path.replaceWith(
          t.callExpression(t.identifier("__rd"), [t.numericLiteral(idCounter.counter++), t.cloneDeep(node)])
        );
      }
    },
  },
};

export function transformAllReactValues() {
  const nodesToWrap = new Set();
  const alreadyVisited = new Set();
  const scopePaths = new Map();
  const idCounter = { counter: 0 };
  traverse(global.ast, ReactValueVisitor, null, { nodesToWrap, alreadyVisited, scopePaths });
  traverse(global.ast, ReactWrapperVisitor, null, { nodesToWrap, idCounter });
  invariant(nodesToWrap.size === 0);
  traverse.cache.clear();
}

function collectRuntimeValuesFromArrayWithNumericWidenedProperty(
  realm: Realm,
  val: ConcreteValue,
  runtimeValues: Set<Value>,
  possibleDeadCodeValues: Set<Value>,
  effects: Effects
): void {
  let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
  invariant(temporalOperationEntry !== undefined);
  let { args, operationDescriptor } = temporalOperationEntry;
  if (operationDescriptor.type === "UNKNOWN_ARRAY_METHOD_PROPERTY_CALL") {
    let [arrayLikeObject, methodProperty, callbackfn] = args;
    invariant(methodProperty instanceof StringValue);
    // For now we only support nested optimized functions on map and filter
    if (methodProperty.value === "map" || methodProperty.value === "filter") {
      collectRuntimeValuesFromFunctionValue(realm, callbackfn, runtimeValues, possibleDeadCodeValues, effects);
      // First arg is the referencing array
      possibleDeadCodeValues.add(val);
      if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(arrayLikeObject)) {
        collectRuntimeValuesFromArrayWithNumericWidenedProperty(
          realm,
          arrayLikeObject,
          runtimeValues,
          possibleDeadCodeValues,
          effects
        );
      } else {
        collectRuntimeValuesFromValue(realm, arrayLikeObject, runtimeValues, possibleDeadCodeValues, effects);
      }
      return;
    }
  } else if (operationDescriptor.type === "UNKNOWN_ARRAY_METHOD_CALL") {
    let [, arrayLikeObject] = args;
    possibleDeadCodeValues.add(val);
    if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(arrayLikeObject)) {
      collectRuntimeValuesFromArrayWithNumericWidenedProperty(
        realm,
        arrayLikeObject,
        runtimeValues,
        possibleDeadCodeValues,
        effects
      );
    } else {
      collectRuntimeValuesFromValue(realm, arrayLikeObject, runtimeValues, possibleDeadCodeValues, effects);
    }
    return;
  }
  runtimeValues.add(val);
}

function collectRuntimeValuesFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  runtimeValues: Set<Value>,
  possibleDeadCodeValues: Set<Value>,
  effects: Effects
): void {
  // if (val.astNode && val.astNode.start === 61236) {
  //   debugger;
  // }
  if (val instanceof ObjectValue) {
    if (!effects.createdObjects.has(val)) {
      // If this object was created outside of the function,
      // then we already know its values
      return;
    }
    for (let [propName, binding] of val.properties) {
      if (binding && binding.descriptor) {
        if (propName === "callee" || propName === "prototype") {
          // Given we don't support cloning functions now, we only check this for other objects
          if (val instanceof FunctionValue) {
            continue;
          }
          invariant(false, "TODO support prototype and callee for non-function objects");
        }
        let propVal = binding.descriptor.value;
        invariant(propVal instanceof Value);
        collectRuntimeValuesFromValue(realm, propVal, runtimeValues, possibleDeadCodeValues, effects);
      }
    }
    if (val instanceof FunctionValue) {
      collectRuntimeValuesFromFunctionValue(realm, val, runtimeValues, possibleDeadCodeValues, effects);
    } else if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      collectRuntimeValuesFromArrayWithNumericWidenedProperty(
        realm,
        val,
        runtimeValues,
        possibleDeadCodeValues,
        effects
      );
    } else {
      invariant(
        val.$Prototype === realm.intrinsics.ObjectPrototype || val.$Prototype === realm.intrinsics.ArrayPrototype
      );
    }
  }
}

function deeplyCheckIfConditionalBranchHasRenderValues(realm: Realm, val: Value): boolean {
  if (val instanceof ObjectValue) {
    return true;
  } else if (val instanceof AbstractValue) {
    if (val.kind === "conditional" || val.kind === "||" || val.kind === "&&") {
      for (let arg of val.args) {
        let check = deeplyCheckIfConditionalBranchHasRenderValues(realm, arg);
        if (check) {
          return true;
        }
      }
    } else if (valueIsKnownReactAbstraction(realm, val)) {
      return true;
    }
  } else if (val instanceof PrimitiveValue) {
    return true;
  }
  return false;
}

function collectRuntimeValuesFromAbstractValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValues: Set<Value>,
  possibleDeadCodeValues: Set<Value>,
  effects: Effects
): void {
  // if (val.astNode && val.astNode.start === 71656) {
  //   debugger;
  // }
  if (!effects.createdAbstracts.has(val)) {
    return val;
  }
  if (runtimeValues.has(val)) {
    return;
  }
  if (valueIsKnownReactAbstraction(realm, val)) {
    invariant(false, "TODO");
  }
  if (val.isTemporal()) {
    // If this property reference is ultimately to a React props object,
    // then we can re-create the temporal chain (without creating runtime values.
    // We can re-model the property access as "props.a.b.c.d" instead.)
    if (isTemporalValueDeeplyReferencingPropsObject(realm, val)) {
      return;
    }
    runtimeValues.add(val);
  } else if (val.kind === "conditional") {
    let [condValue, consequentVal, alternateVal] = val.args;

    // runtimeValues.add(condValue);
    collectRuntimeValuesFromValue(realm, condValue, runtimeValues, possibleDeadCodeValues, effects);
    collectRuntimeValuesFromValue(realm, consequentVal, runtimeValues, possibleDeadCodeValues, effects);
    collectRuntimeValuesFromValue(realm, alternateVal, runtimeValues, possibleDeadCodeValues, effects);
  } else if (val.kind === "||" || val.kind === "&&") {
    let [condValue, rightVal] = val.args;

    // let concreteValues = new Set();
    // getConcreteObjectValuesFromBranch(condValue, concreteValues);
    // if (concreteValues.size > 0) {
    //   collectRuntimeValuesFromValue(realm, condValue, runtimeValues, possibleDeadCodeValues, effects);
    // } else {
    //   runtimeValues.add(condValue);
    // }
    collectRuntimeValuesFromValue(realm, condValue, runtimeValues, possibleDeadCodeValues, effects);
    collectRuntimeValuesFromValue(realm, rightVal, runtimeValues, possibleDeadCodeValues, effects);
  } else if (isAbstractValueBinaryExpression(val) || isAbstractValueUnaryExpression(val)) {
    runtimeValues.add(val);
  } else if (val.kind !== undefined && val.kind.startsWith("template:")) {
    // We can clone templates
  } else if (val.args.length > 0) {
    for (let arg of val.args) {
      collectRuntimeValuesFromValue(realm, arg, runtimeValues, possibleDeadCodeValues, effects);
    }
  } else {
    invariant(false, "TODO");
  }
}

function validateAndMarkRuntimeValuesFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  collectedRuntimeValues: Set<Value>,
  markedRuntimeValues: Set<Value>,
  effects: Effects
) {
  if (val instanceof PrimitiveValue) {
    return; // We don't need to mark primitve values
  }
  invariant(val instanceof ObjectValue);
  if (!effects.createdObjects.has(val)) {
    return; // We don't need to mark objects we created outside the function call
  }
  if (val.isPartialObject() && !realm.react.reactProps.has(val)) {
    invariant(false, "TODO");
  }
  if (val.mightBeLeakedObject()) {
    // We probably have to mark the runtime value
    invariant(false, "TODO");
  }
  for (let [propName, binding] of val.properties) {
    if (binding && binding.descriptor) {
      if (propName === "callee" || propName === "prototype") {
        // Given we don't support cloning functions now, we only check this for other objects
        if (val instanceof FunctionValue) {
          continue;
        }
        invariant(false, "TODO support prototype and callee for non-function objects");
      }
      let propVal = binding.descriptor.value;
      invariant(propVal instanceof Value);
      validateAndMarkRuntimeValuesFromValue(realm, propVal, collectedRuntimeValues, markedRuntimeValues, effects);
    }
  }
  if (val.temporalAlias !== undefined) {
    validateAndMarkRuntimeValuesFromValue(
      realm,
      val.temporalAlias,
      collectedRuntimeValues,
      markedRuntimeValues,
      effects
    );
  }
  // TODO handle unknownProperty
  if (val instanceof FunctionValue) {
    invariant(false, "TODO");
  }
  if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
    invariant(false, "TODO");
  }
}

function validateAndMarkRuntimeValuesFromAbstractValue(
  realm: Realm,
  val: AbstractValue,
  collectedRuntimeValues: Set<Value>,
  markedRuntimeValues: Set<Value>,
  effects: Effects
) {
  if (!effects.createdAbstracts.has(val)) {
    return val; // We don't need to mark abstracts we created outside the function call
  }
  if (val.isTemporal()) {
    if (isTemporalValueDeeplyReferencingPropsObject(realm, val)) {
      // Very much like the case for when we have a partial object value with a temporal alias,
      // we can model this value so we don't need a runtime value. In this case, it's probably best
      // to create a runtime value, to reduce code bloat.
      if (collectedRuntimeValues.has(val)) {
        markedRuntimeValues.add(val);
      }
      return;
    }
    invariant(collectedRuntimeValues.has(val));
    markedRuntimeValues.add(val);
  } else if (val.kind === "conditional") {
    let [condValue, consequentVal, alternateVal] = val.args;
    if (collectedRuntimeValues.has(condValue)) {
      markedRuntimeValues.add(condValue);
    } else {
      // This sucks :(
      debugger;
    }
    let collectionConsequent = true;
    if (collectedRuntimeValues.has(consequentVal)) {
      let hasRenderValues = deeplyCheckIfConditionalBranchHasRenderValues(realm, consequentVal);

      if (!hasRenderValues) {
        // TODO: This value might be a temporal aliasing props
        markedRuntimeValues.add(consequentVal);
        collectionConsequent = false;
      }
    }
    if (collectionConsequent) {
      validateAndMarkRuntimeValuesFromValue(realm, consequentVal, collectedRuntimeValues, markedRuntimeValues, effects);
    }

    let collectionAlternate = true;
    if (collectedRuntimeValues.has(alternateVal)) {
      let hasRenderValues = deeplyCheckIfConditionalBranchHasRenderValues(realm, alternateVal);

      if (!hasRenderValues) {
        // TODO: This value might be a temporal aliasing props
        markedRuntimeValues.add(alternateVal);
        collectionAlternate = false;
      }
    }
    if (collectionAlternate) {
      validateAndMarkRuntimeValuesFromValue(realm, alternateVal, collectedRuntimeValues, markedRuntimeValues, effects);
    }
  } else {
    debugger;
  }
}

function validateAndMarkRuntimeValuesFromValue(
  realm: Realm,
  val: Value,
  collectedRuntimeValues: Set<Value>,
  markedRuntimeValues: Set<Value>,
  effects: Effects
) {
  if (val instanceof ConcreteValue) {
    validateAndMarkRuntimeValuesFromConcreteValue(realm, val, collectedRuntimeValues, markedRuntimeValues, effects);
  } else {
    validateAndMarkRuntimeValuesFromAbstractValue(realm, val, collectedRuntimeValues, markedRuntimeValues, effects);
  }
}

export function getValueFromOutlinedFunctionComponent(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  args: Array<Value>,
  isRoot: boolean
): Value {
  const returnValue = value => {
    let completion = new SimpleNormalCompletion(value);
    return realm.returnOrThrowCompletion(completion);
  };
  // 1. Create a clone of the original function if this is the root of the component tree.
  // Also make all the props deeply final (a constrain added to React component props)
  let clonedFunc;
  if (isRoot) {
    clonedFunc = shallowCloneFunctionValue(realm, func);
  }
  deeplyMakeAllArgsFinal(realm, args);

  // 2. Check if the component render can be inlined and also collect all runtime values.
  // The Babel transform will have already been applied to all relevant functions before
  // this, so we should pick up all dynamic values of interest in collectedRuntimeValues
  // along with the associated IDs of the __rd call that they belong. We can use the ID
  // at a later point to determine which __rd calls can be deadcoded away. We also collect
  // the index of where they come in the values array.
  let collectedRuntimeValues = new Map();
  let [effects, result] = getValueAndEffectsFromFunctionCall(
    realm,
    () => {
      setupEnvironmentForOutlining(realm, collectedRuntimeValues);
      return clonedFunc || func;
    },
    args
  );

  // 3. If the result is primitive or there were no runtime values, then we can safely inline
  // the function call without causing bloat.
  if (result instanceof PrimitiveValue || collectedRuntimeValues.size === 0) {
    if (collectedRuntimeValues.size === 0) {
      console.log("No collected runtime values found");
      debugger;
    }
    return getValueFromFunctionCall(realm, func, realm.intrinsics.undefined, args);
  }

  // 4. Traverse through the result and find all values of interet. As we find them,
  // we validate if they are in our collect runtime values set and if we need them
  // or not. If we need them, we add them to the marked runtime values set.
  const markedRuntimeValues = new Set();
  applyPreviousEffects(realm, effects, () =>
    validateAndMarkRuntimeValuesFromValue(realm, result, collectedRuntimeValues, markedRuntimeValues, effects)
  );

  // 5. Using the marked runtime values and the collected runtime values we collect
  // all runtime value markers we added (__rd) and used. The ones that don't get used
  // can be dead-code eliminated later (via another Babel transform).

  // 6. Fast path optimization for when there are no marked runtime values. We can clone and
  // model the return value given we know everything is static. We also don't outline the
  // function call here as we have no runtime values to reference from it.
  if (markedRuntimeValues.size === 0) {
    let emptyRuntimeValueNameMap = new Map();
    let clonedAndModelledValue = getValueWithPreviousEffectsApplied(realm, effects, () =>
      cloneAndModelValue(realm, result, emptyRuntimeValueNameMap, effects)
    );
    return returnValue(clonedAndModelledValue);
  }

  // 7. We use the marked runtime values set to create a runtime value map of
  // values -> their intrinsic names
  let runtimeValueNameMap = new Map();
  let runtimeValueArrayIntrinsicNames = [];
  for (let [value, { index }] of collectedRuntimeValues) {
    let intrinsicName;
    if (runtimeValueArrayIntrinsicNames[index] === undefined) {
      intrinsicName = runtimeValueArrayIntrinsicNames[index] = realm.preludeGenerator.nameGenerator.generate(
        "outlined"
      );
    } else {
      intrinsicName = runtimeValueArrayIntrinsicNames[index];
    }
    if (markedRuntimeValues.has(value)) {
      runtimeValueNameMap.set(value, intrinsicName);
    }
  }
  // Verify the array does not contain holes
  for (let entry of runtimeValueArrayIntrinsicNames) {
    invariant(entry !== undefined);
  }

  // 8. Emit runtime code to:
  // - Set React values array (__rv) to [], the react values pointer (__ri) to 0
  // - Create a computed function call with original arguments to the original function.
  // - Reference the react values inside the array (__rv)
  let generator = realm.generator;
  invariant(generator !== undefined);
  generator.emitStatement([], createOperationDescriptor("REACT_OUTLINING_CLEAR_REACT_VALUES"));
  generator.emitStatement(
    [clonedFunc || func, ...args],
    createOperationDescriptor("REACT_OUTLINING_ORIGINAL_FUNC_CALL")
  );
  generator.emitStatement(
    runtimeValueArrayIntrinsicNames.map(name => new StringValue(realm, name)),
    createOperationDescriptor("REACT_OUTLINING_REFERENCE_REACT_VALUES")
  );

  // 9. Clone and remodel the return value from the outlined funciton call. This should
  // be a form of ReactElement template, where the slots for dynamic values are assigned in
  // the computed functions and react values array.
  let clonedAndModelledValue = getValueWithPreviousEffectsApplied(realm, effects, () =>
    cloneAndModelValue(realm, result, runtimeValueNameMap, effects)
  );
  return returnValue(clonedAndModelledValue);

  // 5. Generate a set of variable references for each of the runtime variables
  // and map the variable references to the new values
  // let runtimeValueReferenceNames;
  // let runtimeValuesMapping = new Map();

  // applyPreviousEffects(realm, effects, () => {
  //   let reactValues = Get(realm, realm.$GlobalObject, "__rv");
  //   let totalValues = reactValues.properties.size;

  //   runtimeValueReferenceNames = Array.from(Array(totalValues)).map(() =>
  //     realm.preludeGenerator.nameGenerator.generate("outlined")
  //   );

  //   for (let i = 0; i < totalValues; i++) {
  //     let reactValue = Get(realm, reactValues, i + "");
  //     runtimeValuesMapping.set(reactValue, runtimeValueReferenceNames[i]);
  //   }
  // });

  // 7. Emit runtime code to:
  // - Set React values array (__rv) to [], the react values pointer (__ri) to 0
  // - Create a computed function call with original arguments to the original function.
  // - Reference the react values inside the array (__rv)

  // TODO skip this if no values are used?
  // let generator = realm.generator;
  // invariant(generator !== undefined);
  // generator.emitStatement([], createOperationDescriptor("REACT_OUTLINING_CLEAR_REACT_VALUES"));
  // generator.emitStatement(
  //   [clonedFunc || func, ...args],
  //   createOperationDescriptor("REACT_OUTLINING_ORIGINAL_FUNC_CALL")
  // );
  // generator.emitStatement(
  //   runtimeValueReferenceNames.map(name => new StringValue(realm, name)),
  //   createOperationDescriptor("REACT_OUTLINING_REFERENCE_REACT_VALUES")
  // );

  // 8. Clone and remodel the return value from the outlined funciton call. This should
  // be a form of ReactElement template, where the slots for dynamic values are assigned in
  // the computed functions and react values array.
  // let clonedAndModelledValue = getValueWithPreviousEffectsApplied(realm, effects, () =>
  //   cloneAndModelValue(realm, result, runtimeValuesMapping, effects)
  // );
  // return returnValue(clonedAndModelledValue);
}
