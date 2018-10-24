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
import { getInitialProps } from "./components.js";
import traverseFast from "../utils/traverse-fast.js";
import traverse from "@babel/traverse";
import * as t from "@babel/types";
import generate from "@babel/generator";

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

function getConcreteObjectValuesFromBranch(branch: Value, concreteValues: Set<Value>): void {
  if (branch instanceof ObjectValue) {
    concreteValues.add(branch);
  } else if (
    branch instanceof AbstractValue &&
    (branch.type === "conditional" || branch.type === "||" || branch.type === "&&")
  ) {
    for (let arg of branch.args) {
      getConcreteObjectValuesFromBranch(arg, concreteValues);
    }
  }
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

function collectRuntimeValuesFromValue(
  realm: Realm,
  val: Value,
  runtimeValues: Set<Value>,
  possibleDeadCodeValues: Set<Value>,
  effects: Effects
): void {
  if (val instanceof ConcreteValue) {
    collectRuntimeValuesFromConcreteValue(realm, val, runtimeValues, possibleDeadCodeValues, effects);
  } else {
    collectRuntimeValuesFromAbstractValue(realm, val, runtimeValues, possibleDeadCodeValues, effects);
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
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, runtimeValuesMapping, effects);
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
  runtimeValuesMapping: Map<Value, string>,
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
        clonedBinding.value = cloneAndModelValue(realm, binding.value, runtimeValuesMapping, effects);
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
  runtimeValuesMapping: Map<Value, string>,
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
    runtimeValuesMapping,
    effects
  );
  let clonedFunction = Functions.FunctionCreate(realm, val.$FunctionKind, params, body, clonedScope, val.$Strict);
  return clonedFunction;
}

function cloneObjectProperties(
  realm: Realm,
  clonedObject: ObjectValue,
  val: ObjectValue,
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
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
      runtimeValuesMapping,
      effects
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
        runtimeValuesMapping,
        effects
      );
    }
    if (unknownProperty.key !== undefined) {
      key = cloneAndModelValue(realm, unknownProperty.key, runtimeValuesMapping, effects);
    }
    clonedObject.unknownProperty = {
      descriptor: desc,
      key,
      object: clonedObject,
    };
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
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
): Value {
  if (!effects.createdObjects.has(val)) {
    return val;
  }
  if (val instanceof ArrayValue) {
    if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      return cloneAndModelArrayWithNumericWidenedProperty(realm, val, runtimeValuesMapping, effects);
    }
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    cloneObjectProperties(realm, clonedObject, val, runtimeValuesMapping, effects);
    applyPostValueConfig(realm, val, clonedObject);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    if (val instanceof BoundFunctionValue) {
      invariant(false, "TODO");
    }
    invariant(val instanceof ECMAScriptSourceFunctionValue);
    return cloneAndModelFunctionValue(realm, val, runtimeValuesMapping, effects);
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  cloneObjectProperties(realm, clonedObject, val, runtimeValuesMapping, effects);
  applyPostValueConfig(realm, val, clonedObject);
  return clonedObject;
}

function cloneAndModelAbstractTemporalValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
): AbstractValue {
  let intrinsicName = getIntrinsicNameFromTemporalValueDeeplyReferencingPropsObject(realm, val);
  if (realm.react.outlinedTemporalValue.has(intrinsicName)) {
    let abstractValue = realm.react.outlinedTemporalValue.get(intrinsicName);
    invariant(abstractValue !== undefined);
    return abstractValue;
  }
  let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
  invariant(temporalOperationEntry !== undefined);
  let { args, operationDescriptor } = temporalOperationEntry;
  switch (operationDescriptor.type) {
    case "ABSTRACT_PROPERTY": {
      let clonedTemporalArgs = args.map(arg => cloneAndModelValue(realm, arg, runtimeValuesMapping, effects));
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
      let clonedTemporalArgs = args.map(arg => cloneAndModelValue(realm, arg, runtimeValuesMapping, effects));
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
    default:
      invariant(false, "TODO");
  }
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
): Value {
  if (!effects.createdAbstracts.has(val)) {
    return val;
  }
  if (val.isTemporal()) {
    return cloneAndModelAbstractTemporalValue(realm, val, runtimeValuesMapping, effects);
  } else if (val.kind !== undefined) {
    if (val.kind.startsWith("template:")) {
      let source = val.kind.replace("template:", "");
      let clonedArgs = val.args.map(arg => cloneAndModelValue(realm, arg, runtimeValuesMapping, effects));
      return AbstractValue.createFromTemplate(realm, source, val.getType(), clonedArgs);
    } else if (isAbstractValueBinaryExpression(val)) {
      let [leftValue, rightValue] = val.args;
      let clonedLeftValue = cloneAndModelValue(realm, leftValue, runtimeValuesMapping, effects);
      let clonedRightValue = cloneAndModelValue(realm, rightValue, runtimeValuesMapping, effects);
      return AbstractValue.createFromBinaryOp(realm, val.kind, clonedLeftValue, clonedRightValue);
    } else if (isAbstractValueUnaryExpression(val)) {
      let [condValue] = val.args;
      let clonedCondValue = cloneAndModelValue(realm, condValue, runtimeValuesMapping, effects);
      invariant(val.operationDescriptor !== undefined);
      invariant(clonedCondValue instanceof AbstractValue);
      let hasPrefix = val.operationDescriptor.data.prefix;
      return AbstractValue.createFromUnaryOp(realm, val.kind, clonedCondValue, hasPrefix);
    }
    switch (val.kind) {
      case "conditional": {
        let [condValue, consequentVal, alternateVal] = val.args;

        let clonedCondValue = cloneAndModelValue(realm, condValue, runtimeValuesMapping, effects);
        let clonedConsequentVal = cloneAndModelValue(realm, consequentVal, runtimeValuesMapping, effects);
        let clonedAlternateVal = cloneAndModelValue(realm, alternateVal, runtimeValuesMapping, effects);
        return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
      }
      case "||":
      case "&&":
        let [leftValue, rightValue] = val.args;
        let clonedLeftValue = cloneAndModelValue(realm, leftValue, runtimeValuesMapping, effects);
        let clonedRightValue = cloneAndModelValue(realm, rightValue, runtimeValuesMapping, effects);
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
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
): Value {
  if (runtimeValuesMapping.has(val)) {
    let runtimeValue = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
    let intrinsicName = runtimeValuesMapping.get(val);
    invariant(intrinsicName !== undefined);
    runtimeValue.intrinsicName = intrinsicName;
    return runtimeValue;
  }
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, runtimeValuesMapping, effects);
    }
  } else if (val instanceof AbstractValue) {
    return cloneAndModelAbstractValue(realm, val, runtimeValuesMapping, effects);
  }
}

function wrapBabelNodeInRuntimeTransform(astNode: BabelNode) {
  return t.assignmentExpression(
    "=",
    t.memberExpression(t.identifier("__rv"), t.updateExpression("++", t.identifier("__ri")), true),
    astNode
  );
}

function applyBabelTransformForRuntimeValuesOnAstNode(
  realm: Realm,
  astNode: BabelNode,
  mustWrap?: boolean = false
): void {
  let astNodeParent = realm.astNodeParents.get(astNode);
  invariant(astNodeParent !== undefined);

  if (t.isMemberExpression(astNodeParent)) {
    if (mustWrap) {
      invariant(false, "Should never happen");
    }
    applyBabelTransformForRuntimeValuesOnAstNode(realm, astNodeParent);
  } else if (t.isCallExpression(astNodeParent)) {
    if (mustWrap) {
      invariant(false, "Should never happen");
    }
    applyBabelTransformForRuntimeValuesOnAstNode(realm, astNodeParent);
  } else if (t.isJSXExpressionContainer(astNodeParent)) {
    astNodeParent.expression = wrapBabelNodeInRuntimeTransform(astNode);
  } else if (t.isJSXSpreadAttribute(astNodeParent)) {
    astNodeParent.argument = wrapBabelNodeInRuntimeTransform(astNode);
  } else if (t.isIfStatement(astNodeParent)) {
    if (astNodeParent.test === astNode) {
      astNodeParent.test = wrapBabelNodeInRuntimeTransform(astNode);
    } else if (astNodeParent.consequent === astNode) {
      astNodeParent.consequent = wrapBabelNodeInRuntimeTransform(astNode);
    } else if (astNodeParent.alternate === astNode) {
      astNodeParent.alternate = wrapBabelNodeInRuntimeTransform(astNode);
    }
  } else if (t.isVariableDeclarator(astNodeParent)) {
    astNodeParent.init = wrapBabelNodeInRuntimeTransform(astNode);
  } else if (t.isLogicalExpression(astNodeParent)) {
    if (mustWrap) {
      if (astNodeParent.left === astNode) {
        astNodeParent.left = wrapBabelNodeInRuntimeTransform(astNode);
      } else if (astNodeParent.right === astNode) {
        astNodeParent.right = wrapBabelNodeInRuntimeTransform(astNode);
      }
    } else {
      applyBabelTransformForRuntimeValuesOnAstNode(realm, astNodeParent);
    }
  } else if (t.isConditionalExpression(astNodeParent)) {
    if (astNodeParent.test === astNode) {
      astNodeParent.test = wrapBabelNodeInRuntimeTransform(astNode);
    } else if (astNodeParent.consequent === astNode) {
      astNodeParent.consequent = wrapBabelNodeInRuntimeTransform(astNode);
    } else if (astNodeParent.alternate === astNode) {
      astNodeParent.alternate = wrapBabelNodeInRuntimeTransform(astNode);
    }
  } else if (t.isBinaryExpression(astNodeParent)) {
    if (mustWrap) {
      invariant(false, "Should never happen");
    }
    applyBabelTransformForRuntimeValuesOnAstNode(realm, astNodeParent);
  } else if (t.isReturnStatement(astNodeParent)) {
    astNodeParent.argument = wrapBabelNodeInRuntimeTransform(astNode);
  } else if (t.isObjectProperty(astNodeParent)) {
    astNodeParent.value = wrapBabelNodeInRuntimeTransform(astNode);
  } else if (t.isUnaryExpression(astNodeParent)) {
    if (mustWrap) {
      invariant(false, "Should never happen");
    }
    applyBabelTransformForRuntimeValuesOnAstNode(realm, astNodeParent);
  } else if (t.isAssignmentExpression(astNodeParent)) {
    astNodeParent.right = astNode;
  } else if (t.isArrayExpression(astNodeParent)) {
    for (let i = 0; i < astNodeParent.elements.length; i++) {
      let element = astNodeParent.elements[i];
      if (element === astNode) {
        astNodeParent.elements[i] = wrapBabelNodeInRuntimeTransform(astNode);
        break;
      }
    }
  } else if (t.isArrowFunctionExpression(astNodeParent)) {
    astNodeParent.body = wrapBabelNodeInRuntimeTransform(astNode);
  } else {
    invariant(false, "TODO");
  }
}

function wrapBabelNodeInDeadcodeTransform(astNode: BabelNode) {
  return t.callExpression(t.identifier("__possibleDeadCode"), [astNode]);
}

function applyBabelTransformForDeadCodeOnAstNode(realm: Realm, astNode: BabelNode): void {
  let astNodeParent = realm.astNodeParents.get(astNode);
  invariant(astNodeParent !== undefined);

  if (t.isMemberExpression(astNodeParent)) {
    applyBabelTransformForDeadCodeOnAstNode(realm, astNodeParent);
  } else if (t.isCallExpression(astNodeParent)) {
    applyBabelTransformForDeadCodeOnAstNode(realm, astNodeParent);
  } else if (t.isVariableDeclarator(astNodeParent)) {
    if (astNodeParent.init === astNode) {
      astNodeParent.init = wrapBabelNodeInDeadcodeTransform(astNode);
    } else {
      invariant(false, "TODO not possible to get here?");
    }
  } else {
    invariant(false, "TODO");
  }
}

function applyBabelTransformsWithRuntimeValues(
  realm: Realm,
  runtimeValues: Set<Value>,
  possibleDeadCodeValues: Set<Value>
): void {
  const markContainingFunction = astNode => {
    while (astNode !== undefined) {
      if (t.isFunctionExpression(astNode) || t.isFunctionDeclaration(astNode)) {
        realm.react.outlinedFunctionAstNodes.add(astNode);
        break;
      }
      astNode = realm.astNodeParents.get(astNode);
    }
  };

  for (let runtimeValue of runtimeValues) {
    let astNode = runtimeValue.astNode;
    invariant(astNode !== undefined);
    if (
      runtimeValue instanceof AbstractValue &&
      (runtimeValue.kind === "||" || runtimeValue.kind === "&&") &&
      (t.isLogicalExpression(astNode) || t.isCallExpression(astNode))
    ) {
      applyBabelTransformForRuntimeValuesOnAstNode(realm, astNode, true);
    } else {
      applyBabelTransformForRuntimeValuesOnAstNode(realm, astNode, false);
    }
    markContainingFunction(astNode);
  }
  for (let possibleDeadCodeValue of possibleDeadCodeValues) {
    let astNode = possibleDeadCodeValue.astNode;
    invariant(astNode !== undefined);
    // applyBabelTransformForDeadCodeOnAstNode(realm, astNode);
    markContainingFunction(astNode);
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

function setupEnvironmentForOutlining(realm: Realm) {
  realm.react.usedOutlinedValuesArray = true;
  // ensure we define a global value for bindings __rv and __ri in Prepack
  let globalObject = realm.$GlobalObject;
  let __rv = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  __rv.makeFinal();
  realm.react.reactValueArrays.add(__rv);
  globalObject.$DefineOwnProperty(
    "__rv",
    new PropertyDescriptor({
      value: __rv,
      writable: true,
      enumerable: false,
      configurable: true,
    })
  );
  let __ri = 0;
  globalObject.$DefineOwnProperty(
    "__ri",
    new PropertyDescriptor({
      get: new NativeFunctionValue(realm, undefined, undefined, 0, (context, [requireNameVal]) => {
        return new NumberValue(realm, __ri);
      }),
      set: new NativeFunctionValue(realm, undefined, undefined, 0, (context, [newValue]) => {
        invariant(newValue instanceof NumberValue);
        __ri = newValue.value;
        return newValue;
      }),
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
  realm.astNodeParents.set(body, t.functionExpression(t.identifier("__shallowCloneFunctionValue__"), params, body));
  traverseFast(body, null, (node, parentNode) => {
    if (parentNode !== null) realm.astNodeParents.set(node, parentNode);
    if (!t.isIdentifier(node)) return false;
  });
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

function shouldInlineFunctionalComponent(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  args: Array<Value>
): boolean {
  let [, result] = getValueAndEffectsFromFunctionCall(
    realm,
    () => {
      setupEnvironmentForOutlining(realm);
      return func;
    },
    args
  );

  // If the result is primitive, we always inline the function call.
  if (result instanceof PrimitiveValue) {
    return true;
  }
  return false;
}

function createRuntimeValuesAndApplyBabelTransform(realm: Realm, func: ECMAScriptSourceFunctionValue): Set<Values> {
  if (realm.react.outlinedFunctionInformation.has(func)) {
    let runtimeValues = realm.react.outlinedFunctionInformation.get(func);
    invariant(runtimeValues !== undefined);
    return runtimeValues;
  }
  let args = [getInitialProps(realm, func, {})];
  let [effects, result] = getValueAndEffectsFromFunctionCall(realm, func, args);
  let runtimeValues = new Set();
  let possibleDeadCodeValues = new Set();

  applyPreviousEffects(realm, effects, () => {
    collectRuntimeValuesFromValue(realm, result, runtimeValues, possibleDeadCodeValues, effects);
  });
  applyBabelTransformsWithRuntimeValues(realm, runtimeValues, possibleDeadCodeValues);

  realm.react.outlinedFunctionInformation.set(func, runtimeValues);
  return runtimeValues;
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
    // clonedFunc = shallowCloneFunctionValue(realm, func);
  }
  deeplyMakeAllArgsFinal(realm, args);

  // 2. First check if the component render can be inlined
  if (shouldInlineFunctionalComponent(realm, clonedFunc || func, args)) {
    return getValueFromFunctionCall(realm, func, realm.intrinsics.undefined, args);
  }

  // 3. Now we need to find all the runtime values for the given function.
  // Furthermore, we apply code transforms so that runtime values are collected.
  // If this was done on the same function at a previous point this will be a no-op.
  let runtimeValues = createRuntimeValuesAndApplyBabelTransform(realm, clonedFunc || func);

  printAst();
  // 4. Evaluate the component render again, this time with the args we were given.
  // Furthermore, we are now evaluating code that has had code transforms applied.
  let [babelTransformedEffects, babelTransformedResult] = getValueAndEffectsFromFunctionCall(
    realm,
    () => {
      setupEnvironmentForOutlining(realm);
      return clonedFunc || func;
    },
    args
  );

  // 5. Generate a set of variable references for each of the runtime variables
  // and map the variable references to the new values
  let runtimeValueReferenceNames;
  let runtimeValuesMapping = new Map();

  applyPreviousEffects(realm, babelTransformedEffects, () => {
    let reactValues = Get(realm, realm.$GlobalObject, "__rv");
    let totalValues = reactValues.properties.size;

    runtimeValueReferenceNames = Array.from(Array(totalValues)).map(() =>
      realm.preludeGenerator.nameGenerator.generate("outlined")
    );

    for (let i = 0; i < totalValues; i++) {
      let reactValue = Get(realm, reactValues, i + "");
      runtimeValuesMapping.set(reactValue, runtimeValueReferenceNames[i]);
    }
  });

  // 7. Emit runtime code to:
  // - Set React values array (__rv) to [], the react values pointer (__ri) to 0
  // - Create a computed function call with original arguments to the original function.
  // - Reference the react values inside the array (__rv)
  if (runtimeValues.size > 0) {
    let generator = realm.generator;
    invariant(generator !== undefined);
    generator.emitStatement([], createOperationDescriptor("REACT_OUTLINING_CLEAR_REACT_VALUES"));
    generator.emitStatement(
      [clonedFunc || func, ...args],
      createOperationDescriptor("REACT_OUTLINING_ORIGINAL_FUNC_CALL")
    );
    generator.emitStatement(
      runtimeValueReferenceNames.map(name => new StringValue(realm, name)),
      createOperationDescriptor("REACT_OUTLINING_REFERENCE_REACT_VALUES")
    );
  }

  // 8. Clone and remodel the return value from the outlined funciton call. This should
  // be a form of ReactElement template, where the slots for dynamic values are assigned in
  // the computed functions and react values array.
  let clonedAndModelledValue = getValueWithPreviousEffectsApplied(realm, babelTransformedEffects, () =>
    cloneAndModelValue(realm, babelTransformedResult, runtimeValuesMapping, babelTransformedEffects)
  );
  return returnValue(clonedAndModelledValue);
}

function printAst() {
  console.log(generate(global.ast).code);
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
