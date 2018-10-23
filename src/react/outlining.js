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
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import {
  AbstractValue,
  ArrayValue,
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

function collectRuntimeValuesFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  runtimeValues: Set<Value>,
  effects: Effects
): void {
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
        let propVal = Get(realm, val, propName);
        collectRuntimeValuesFromValue(realm, propVal, runtimeValues, effects);
      }
    }
    if (val instanceof FunctionValue) {
      invariant(false, "TODO");
    } else if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      invariant(false, "TODO");
    } else {
      invariant(
        val.$Prototype === realm.intrinsics.ObjectPrototype || val.$Prototype === realm.intrinsics.ArrayPrototype
      );
    }
  }
}

function collectRuntimeValuesFromAbstractValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValues: Set<Value>,
  effects: Effects
): void {
  if (!effects.createdAbstracts.has(val)) {
    // If this abstract was created outside of the function,
    // then we already know its values
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
    let condRuntimeValues = new Set();
    collectRuntimeValuesFromValue(realm, condValue, condRuntimeValues, effects);
    if (condRuntimeValues.size > 0) {
      runtimeValues.add(condValue);
    }
    collectRuntimeValuesFromValue(realm, consequentVal, runtimeValues, effects);
    collectRuntimeValuesFromValue(realm, alternateVal, runtimeValues, effects);
  } else if (val.args.length > 0) {
    for (let arg of val.args) {
      collectRuntimeValuesFromValue(realm, arg, runtimeValues, effects);
    }
  } else {
    invariant(false, "TODO");
  }
}

function collectRuntimeValuesFromValue(realm: Realm, val: Value, runtimeValues: Set<Value>, effects: Effects): void {
  if (val instanceof ConcreteValue) {
    collectRuntimeValuesFromConcreteValue(realm, val, runtimeValues, effects);
  } else {
    collectRuntimeValuesFromAbstractValue(realm, val, runtimeValues, effects);
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
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    cloneObjectProperties(realm, clonedObject, val, runtimeValuesMapping, effects);
    applyPostValueConfig(realm, val, clonedObject);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    debugger;
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
  if (realm.react.outlinedTemporalAbstract.has(intrinsicName)) {
    let abstractValue = realm.react.outlinedTemporalAbstract.get(intrinsicName);
    invariant(abstractValue !== undefined);
    return abstractValue;
  }
  let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
  invariant(temporalOperationEntry !== undefined);
  let { args, operationDescriptor } = temporalOperationEntry;
  switch (operationDescriptor.type) {
    case "ABSTRACT_PROPERTY": {
      let clonedTemporalArgs = args.map(arg => cloneAndModelValue(realm, arg, runtimeValuesMapping, effects));
      let abstractValue = AbstractValue.createFromBuildFunction(
        realm,
        val.getType(),
        clonedTemporalArgs,
        createOperationDescriptor("ABSTRACT_PROPERTY"),
        { kind: val.kind, isPure: temporalOperationEntry.isPure, skipInvariant: temporalOperationEntry.skipInvariant }
      );
      realm.react.outlinedTemporalAbstract.set(intrinsicName, abstractValue);
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
      realm.react.outlinedTemporalAbstract.set(intrinsicName, abstractValue);
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
    switch (val.kind) {
      case "conditional": {
        let [condValue, consequentVal, alternateVal] = val.args;
        let clonedCondValue = cloneAndModelValue(realm, condValue, runtimeValuesMapping, effects);
        let clonedConsequentVal = cloneAndModelValue(realm, consequentVal, runtimeValuesMapping, effects);
        let clonedAlternateVal = cloneAndModelValue(realm, alternateVal, runtimeValuesMapping, effects);
        return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
      }
      case "!":
      case "typeof":
      case "delete":
      case "+":
      case "-":
      case "void":
      case "~": {
        // Unary ops
        let [condValue] = val.args;
        let clonedCondValue = cloneAndModelValue(realm, condValue, runtimeValuesMapping, effects);
        invariant(val.operationDescriptor !== undefined);
        invariant(clonedCondValue instanceof AbstractValue);
        let hasPrefix = val.operationDescriptor.data.prefix;
        return AbstractValue.createFromUnaryOp(realm, val.kind, clonedCondValue, hasPrefix);
      }
      case "||":
      case "&&":
        // Logical ops
        let [leftValue, rightValue] = val.args;
        let clonedLeftValue = cloneAndModelValue(realm, leftValue, runtimeValuesMapping, effects);
        let clonedRightValue = cloneAndModelValue(realm, rightValue, runtimeValuesMapping, effects);
        return AbstractValue.createFromLogicalOp(realm, val.kind, clonedLeftValue, clonedRightValue);
      default:
        invariant(false, "TODO");
    }
  }
  debugger;
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

function wrapBabelNodeInTransform(astNode: BabelNode) {
  return t.assignmentExpression(
    "=",
    t.memberExpression(t.identifier("__rv"), t.updateExpression("++", t.identifier("__ri")), true),
    astNode
  );
}

function applyBabelTransformOnAstNode(realm: Realm, astNode: BabelNode): void {
  let astNodeParent = realm.astNodeParents.get(astNode);
  invariant(astNodeParent !== undefined);

  if (t.isMemberExpression(astNodeParent)) {
    applyBabelTransformOnAstNode(realm, astNodeParent);
  } else if (t.isCallExpression(astNodeParent)) {
    applyBabelTransformOnAstNode(realm, astNodeParent);
  } else if (t.isJSXExpressionContainer(astNodeParent)) {
    astNodeParent.expression = wrapBabelNodeInTransform(astNode);
  } else if (t.isIfStatement(astNodeParent)) {
    if (astNodeParent.test === astNode) {
      astNodeParent.test = wrapBabelNodeInTransform(astNode);
    } else if (astNodeParent.consequent === astNode) {
      astNodeParent.consequent = wrapBabelNodeInTransform(astNode);
    } else {
      astNodeParent.alternate = wrapBabelNodeInTransform(astNode);
    }
  } else if (t.isVariableDeclarator(astNodeParent)) {
    if (astNodeParent.init === astNode) {
      astNodeParent.init = wrapBabelNodeInTransform(astNode);
    } else {
      invariant(false, "TODO not possible to get here?");
    }
  } else if (t.isLogicalExpression(astNodeParent)) {
    applyBabelTransformOnAstNode(realm, astNodeParent);
  } else {
    invariant(false, "TODO");
  }
}

function applyBabelTransformsWithRuntimeValues(realm: Realm, runtimeValues: Set<Value>): void {
  for (let runtimeValue of runtimeValues) {
    let astNode = runtimeValue.astNode;
    invariant(astNode !== undefined);
    applyBabelTransformOnAstNode(realm, astNode);
    // Mark the function that the astNode is in
    while (astNode !== undefined) {
      if (t.isFunctionExpression(astNode) || t.isFunctionDeclaration(astNode)) {
        realm.react.outlinedFunctionAstNodes.add(astNode);
        break;
      }
      astNode = realm.astNodeParents.get(astNode);
    }
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

  applyPreviousEffects(realm, effects, () => {
    collectRuntimeValuesFromValue(realm, result, runtimeValues, effects);
  });
  applyBabelTransformsWithRuntimeValues(realm, runtimeValues);

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
    clonedFunc = shallowCloneFunctionValue(realm, func);
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
  let runtimeValueReferenceNames = Array.from(Array(runtimeValues.size)).map(() =>
    realm.preludeGenerator.nameGenerator.generate("outlined")
  );

  let runtimeValuesMapping = new Map();

  // 6. Map the variable references to the new values
  applyPreviousEffects(realm, babelTransformedEffects, () => {
    let reactValues = Get(realm, realm.$GlobalObject, "__rv");

    for (let i = 0; i < runtimeValues.size; i++) {
      let reactValue = Get(realm, reactValues, i + "");
      invariant(reactValue !== realm.intrinsics.undefined);
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
        parentNode.alternative = createNewNode(path, node);
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
};

export function stripDeadReactElementNodes(realm: Realm): void {
  for (let outlinedFunctionAstNode of realm.react.outlinedFunctionAstNodes) {
    let node = t.isFunctionExpression(outlinedFunctionAstNode)
      ? t.expressionStatement(outlinedFunctionAstNode)
      : outlinedFunctionAstNode;
    traverse(t.file(t.program([node])), ReactElementVisitor, null, null);
  }
  traverse.cache.clear();
}
