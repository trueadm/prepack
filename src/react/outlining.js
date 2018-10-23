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
  NumberValue,
  ObjectValue,
  PrimitiveValue,
  StringValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { Get } from "../methods/index.js";
import {
  getValueFromFunctionCall,
  isTemporalValueDeeplyReferencingPropsObject,
  valueIsKnownReactAbstraction,
} from "./utils.js";
import { Create, Functions, Properties } from "../singletons.js";
import { cloneDescriptor, PropertyDescriptor } from "../descriptors.js";
import { createOperationDescriptor } from "../utils/generator.js";
import traverseFast from "../utils/traverse-fast.js";
import * as t from "@babel/types";

function collectRuntimeValuesFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  inUnknownConditional: boolean,
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
        collectRuntimeValuesFromValue(realm, propVal, inUnknownConditional, runtimeValues, effects);
      }
    }
    if (val instanceof FunctionValue) {
      // TODO
      debugger;
    } else if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      // TODO
      debugger;
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
  inUnknownConditional: boolean,
  runtimeValues: Set<Value>,
  effects: Effects
): void {
  if (!effects.createdAbstracts.has(val)) {
    // If this abstract was created outside of the function,
    // then we already know its values
    return;
  }
  if (valueIsKnownReactAbstraction(realm, val)) {
    // TODO
    debugger;
  }
  if (val.isTemporal()) {
    // If this property reference is ultimately to a React props object,
    // then we can re-create the temporal chain (without creating runtime values.
    // We can re-model the property access as "props.a.b.c.d" instead.)
    if (isTemporalValueDeeplyReferencingPropsObject(realm, val)) {
      return;
    }
    runtimeValues.add(val);
  } else {
    debugger;
  }
}

function collectRuntimeValuesFromValue(
  realm: Realm,
  val: Value,
  inUnknownConditional: boolean,
  runtimeValues: Set<Value>,
  effects: Effects
): void {
  if (val instanceof ConcreteValue) {
    collectRuntimeValuesFromConcreteValue(realm, val, inUnknownConditional, runtimeValues, effects);
  } else {
    collectRuntimeValuesFromAbstractValue(realm, val, inUnknownConditional, runtimeValues, effects);
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

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValuesMapping: Map<Value, string>,
  effects: Effects
): Value {
  if (!effects.createdAbstracts.has(val)) {
    return val;
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

function applyBabelTransformOnAstNode(realm: Realm, astNode: BabelNode, foundNodeToWrap?: boolean = false): void {
  let astNodeParent = realm.astNodeParents.get(astNode);
  invariant(astNodeParent !== undefined);

  if (t.isMemberExpression(astNodeParent)) {
    applyBabelTransformOnAstNode(realm, astNodeParent, foundNodeToWrap);
  } else if (t.isCallExpression(astNodeParent)) {
    if (astNodeParent.callee === astNode) {
      if (foundNodeToWrap) {
        astNodeParent.callee = wrapBabelNodeInTransform(astNode);
      } else {
        applyBabelTransformOnAstNode(realm, astNodeParent, true);
      }
    } else {
      invariant(false, "TODO arguments");
    }
  } else if (t.isJSXExpressionContainer(astNodeParent)) {
    astNodeParent.expression = wrapBabelNodeInTransform(astNode);
  } else {
    debugger;
  }
}

function applyBabelTransformsWithRuntimeValues(realm: Realm, runtimeValues: Set<Value>): void {
  for (let runtimeValue of runtimeValues) {
    let astNode = runtimeValue.astNode;
    invariant(astNode !== undefined);
    applyBabelTransformOnAstNode(realm, astNode);
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
    debugger;
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    debugger;
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  return [effects, result];
}

function setupEnvironmentForOutlining(realm: Realm) {
  realm.react.usedOutlinedValuesArray = true;
  // ensure we define a global value for bindings __rv and __ri in Prepack
  let globalObject = realm.$GlobalObject;
  globalObject.$DefineOwnProperty(
    "__rv",
    new PropertyDescriptor({
      value: Create.ArrayCreate(realm, 0),
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
}

function shallowCloneFunctionValue(realm: Realm, func: ECMAScriptSourceFunctionValue): ECMAScriptSourceFunctionValue {
  if (realm.react.clonedOutlinedFunctions.has(func)) {
    let clonedFunc = realm.react.clonedOutlinedFunctions.get(func);
    invariant(clonedFunc instanceof ECMAScriptSourceFunctionValue);
    return clonedFunc;
  }
  let body = ((t.cloneDeep(t.blockStatement([func.$ECMAScriptCode])): any): BabelNodeBlockStatement);
  let params = func.$FormalParameters;
  invariant(func.isValid());
  let clonedFunc = Functions.FunctionCreate(realm, func.$FunctionKind, params, body, func.$Environment, func.$Strict);
  realm.react.clonedOutlinedFunctions.set(func, clonedFunc);
  traverseFast(body, null, (node, parentNode) => {
    if (parentNode !== null) realm.astNodeParents.set(node, parentNode);
    if (!t.isIdentifier(node)) return false;
  });
  return clonedFunc;
}

export function getValueFromOutlinedFunctionComponent(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  args: Array<Value>
): Value {
  const returnValue = value => {
    let completion = new SimpleNormalCompletion(value);
    return realm.returnOrThrowCompletion(completion);
  };
  // 1. Create a clone of the original function (so we don't mutate the original)
  let clonedFunc = shallowCloneFunctionValue(realm, func);

  // 1. Evalaute the original component render, getting the renderered return value
  // as if the entire component was inlined.
  let [effects, result] = getValueAndEffectsFromFunctionCall(realm, clonedFunc, args);

  // If the result is primitive, we always inline the function call.
  if (result instanceof PrimitiveValue) {
    console.log("Primitive value");
    realm.applyEffects(effects);
    return returnValue(result);
  }
  let runtimeValues = new Set();

  // 2. Collect all runtime values from the renderered return value.
  applyPreviousEffects(realm, effects, () => {
    collectRuntimeValuesFromValue(realm, result, false, runtimeValues, effects);
  });

  if (runtimeValues.size === 0) {
    // Given there are no runtime values, we can inline
    console.log("No runtime values");
    realm.applyEffects(effects);
    return returnValue(result);
  }
  // Emit __rv = []; (runtimeValues array)
  let generator = realm.generator;
  invariant(generator !== undefined);

  // 3. Apply a Babel transform to cloned function that adds runtime value capturing.
  applyBabelTransformsWithRuntimeValues(realm, runtimeValues);

  // 4. Evaluate the component render again, this time using the Babel transformed code.
  let [babelTransformedEffects, babelTransformedResult] = getValueAndEffectsFromFunctionCall(
    realm,
    () => {
      setupEnvironmentForOutlining(realm);
      return clonedFunc;
    },
    args
  );

  // 5. Generate a set of variable references for each of the runtime variables
  let runtimeValueReferenceNames = Array.of(runtimeValues.size).map(() =>
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
  generator.emitStatement([], createOperationDescriptor("REACT_OUTLINING_CLEAR_REACT_VALUES"));
  generator.emitStatement([clonedFunc, ...args], createOperationDescriptor("REACT_OUTLINING_ORIGINAL_FUNC_CALL"));
  generator.emitStatement(
    runtimeValueReferenceNames.map(name => new StringValue(realm, name)),
    createOperationDescriptor("REACT_OUTLINING_REFERENCE_REACT_VALUES")
  );

  // 8. Clone and remodel the return value from the outlined funciton call. This should
  // be a form of ReactElement template, where the slots for dynamic values are assigned in
  // the computed functions and react values array.
  let clonedAndModelledValue = getValueWithPreviousEffectsApplied(realm, babelTransformedEffects, () =>
    cloneAndModelValue(realm, babelTransformedResult, runtimeValuesMapping, babelTransformedEffects)
  );
  return returnValue(clonedAndModelledValue);
}
