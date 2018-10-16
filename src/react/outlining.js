/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { Realm } from "../realm.js";
import {
  AbstractValue,
  ArrayValue,
  BoundFunctionValue,
  ConcreteValue,
  ECMAScriptFunctionValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  PrimitiveValue,
  ObjectValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import { PropertyDescriptor, cloneDescriptor } from "../descriptors.js";
import { Get } from "../methods/index.js";
import { Properties, Utils } from "../singletons.js";

function getOutliningValuesFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Set<Value>
): void {
  if (val instanceof PrimitiveValue) {
    knownValues.add(val);
  } else if (val instanceof ObjectValue) {
    if (funcEffects !== undefined && !funcEffects.createdObjects.has(val)) {
      knownValues.add(val);
      return;
    }
    for (let [propName, binding] of val.properties) {
      if (binding && binding.descriptor) {
        // TODO support prototypes and callee
        if (propName === "callee" || propName === "prototype") {
          // Given we don't support cloning functions now, we only check this for other objects
          if (val instanceof FunctionValue) {
            continue;
          }
          invariant(false, "TODO support prototype and callee for non-function objects");
        }
        invariant(val instanceof ObjectValue);
        let propVal = Get(realm, val, propName);
        getOutliningValues(realm, propVal, funcEffects, knownValues, clonableValues, unknownValues);
      }
    }
    if (val instanceof ArrayValue) {
      invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
      clonableValues.add(val);
    } else if (val instanceof FunctionValue) {
      invariant(val.$Prototype === realm.intrinsics.FunctionPrototype);
      // we don't handle unknown values just yet
      unknownValues.add(val);
    } else {
      invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
      clonableValues.add(val);
    }
  }
}

function getOutliningValuesFromAbstractValue(
  realm: Realm,
  val: AbstractValue,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Set<Value>,
  noCloningAbstracts?: boolean
): void {
  if (!funcEffects.createdAbstracts.has(val)) {
    knownValues.add(val);
    return;
  }
  if (noCloningAbstracts) {
    unknownValues.add(val);
    return;
  }
  if (val.kind === "conditional") {
    clonableValues.add(val);
    let [condValue, consequentVal, alternateVal] = val.args;
    getOutliningValues(realm, condValue, funcEffects, knownValues, clonableValues, unknownValues, true);
    getOutliningValues(realm, consequentVal, funcEffects, knownValues, clonableValues, unknownValues);
    getOutliningValues(realm, alternateVal, funcEffects, knownValues, clonableValues, unknownValues);
  } else if (val.args.length > 0) {
    clonableValues.add(val);
    for (let arg of val.args) {
      getOutliningValues(realm, arg, funcEffects, knownValues, clonableValues, unknownValues);
    }
  } else {
    unknownValues.add(val);
  }
}

function getOutliningValues(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Set<Value>,
  noCloningAbstracts?: boolean
): void {
  if (val instanceof ConcreteValue) {
    return getOutliningValuesFromConcreteValue(realm, val, funcEffects, knownValues, clonableValues, unknownValues);
  } else if (val instanceof AbstractValue) {
    return getOutliningValuesFromAbstractValue(
      realm,
      val,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      noCloningAbstracts
    );
  }
  invariant(false, "unknown value type found in getOutliningValues");
}

function modelAndOptimizeOutlinedFunction(realm: Realm, func: ECMAScriptFunctionValue, thisValue: Value): void {
  let funcToModel;
  if (func instanceof BoundFunctionValue) {
    funcToModel = func.$BoundTargetFunction;
    thisValue = func.$BoundThis;
  } else {
    funcToModel = func;
  }
  invariant(funcToModel instanceof ECMAScriptSourceFunctionValue);
  // We only need to optimize the function once
  if (realm.collectedNestedOptimizedFunctionEffects.has(funcToModel)) {
    return;
  }
  let funcCall = () => {
    return realm.evaluateFunctionForPureEffects(
      funcToModel,
      Utils.createModelledFunctionCall(realm, funcToModel, undefined, thisValue),
      null,
      "outlining modelAndOptimizeOutlinedFunction",
      () => {
        debugger;
      }
    );
  };

  let effects = realm.isInPureScope() ? funcCall() : realm.evaluateWithPureScope(funcCall);
  realm.collectedNestedOptimizedFunctionEffects.set(funcToModel, { effects, thisValue });
}

export function possiblyOutlineFunctionCall(
  realm: Realm,
  F: ECMAScriptFunctionValue,
  thisArgument: Value,
  argsList: Array<Value>,
  effects: Effects
): Value {
  let result = effects.result;
  if (result instanceof AbruptCompletion) {
    debugger;
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    debugger;
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  invariant(result instanceof Value);
  const inlineFunctionCall = () => {
    realm.applyEffects(effects);
    return realm.returnOrThrowCompletion(effects.result);
  };
  let usesThis = thisArgument !== realm.intrinsics.undefined;
  let isPrimitive = result instanceof PrimitiveValue;

  if (isPrimitive || !Utils.areEffectsPure(realm, effects, F)) {
    return inlineFunctionCall();
  }
  let knownValues = new Set();
  let clonableValues = new Set();
  let unknownValues = new Set();
  realm.withEffectsAppliedInGlobalEnv(() => {
    getOutliningValues(realm, result, effects, knownValues, clonableValues, unknownValues);
    return realm.intrinsics.undefined;
  }, effects);
  modelAndOptimizeOutlinedFunction(realm, F, thisArgument);
  return AbstractValue.createOutlinedFunctionMarker(
    realm,
    F,
    argsList,
    knownValues,
    clonableValues,
    unknownValues,
    effects
  );
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
  value.modeled = true;
}

function cloneAndModelObjectPropertyDescriptor(
  realm: Realm,
  object: ObjectValue,
  clonedObject: ObjectValue,
  propName: string,
  desc: PropertyDescriptor,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Map<Value, string>
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, funcEffects, knownValues, clonableValues, unknownValues);
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
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Map<Value, string>
): void {
  clonedObject.refuseSerialization = true;
  for (let [propName, { descriptor }] of val.properties) {
    // TODO support prototypes and callee
    if (propName === "prototype" || propName === "callee") {
      invariant(false, "TODO support prototype and callee");
    }
    invariant(descriptor instanceof PropertyDescriptor);
    let desc = cloneAndModelObjectPropertyDescriptor(
      realm,
      val,
      clonedObject,
      propName,
      descriptor,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues
    );
    Properties.OrdinaryDefineOwnProperty(realm, clonedObject, propName, desc);
  }
  clonedObject.refuseSerialization = false;
}

function cloneAndModelObjectValue(
  realm: Realm,
  val: ObjectValue,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Map<Value, string>
): ObjectValue {
  if (knownValues.has(val)) {
    return val;
  }
  if (val instanceof ArrayValue) {
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    cloneObjectProperties(realm, clonedObject, val, funcEffects, knownValues, clonableValues, unknownValues);
    applyPostValueConfig(realm, val, clonedObject);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    invariant(val.$Prototype === realm.intrinsics.FunctionPrototype);
    if (unknownValues.has(val)) {
      let intrinsicName = unknownValues.get(val);
      let clonedAbstractValue = AbstractValue.createFromType(realm, val.getType(), "outlined abstract intrinsic", []);
      clonedAbstractValue.intrinsicName = intrinsicName;
      return clonedAbstractValue;
    }
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  invariant(clonableValues.has(val));
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  cloneObjectProperties(realm, clonedObject, val, funcEffects, knownValues, clonableValues, unknownValues);
  applyPostValueConfig(realm, val, clonedObject);
  return clonedObject;
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Map<Value, string>
): ObjectValue {
  if (knownValues.has(val)) {
    return val;
  }
  const kind = val.kind;
  if (kind === "outlined function marker") {
    return getModeledValueFromOutlinedFunctionMaker(realm, val, unknownValues);
  }
  if (unknownValues.has(val)) {
    let intrinsicName = unknownValues.get(val);
    let clonedAbstractValue = AbstractValue.createFromType(realm, val.getType(), "outlined abstract intrinsic", []);
    clonedAbstractValue.intrinsicName = intrinsicName;
    return clonedAbstractValue;
  }
  if (kind === "conditional") {
    invariant(clonableValues.has(val));
    // Conditional ops
    let [condValue, consequentVal, alternateVal] = val.args;
    let clonedCondValue = cloneAndModelValue(realm, condValue, funcEffects, knownValues, clonableValues, unknownValues);
    let clonedConsequentVal = cloneAndModelValue(
      realm,
      consequentVal,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues
    );
    let clonedAlternateVal = cloneAndModelValue(
      realm,
      alternateVal,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues
    );
    return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
  } else if (kind === "&&" || kind === "||") {
    invariant(clonableValues.has(val));
    // Logical ops
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(realm, leftValue, funcEffects, knownValues, clonableValues, unknownValues);
    let clonedRightValue = cloneAndModelValue(
      realm,
      rightValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues
    );
    return AbstractValue.createFromLogicalOp(realm, kind, clonedLeftValue, clonedRightValue);
  } else if (
    kind === "+" ||
    kind === "-" ||
    kind === "!=" ||
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
    kind === "*"
  ) {
    invariant(clonableValues.has(val));
    // Binary ops
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(realm, leftValue, funcEffects, knownValues, clonableValues, unknownValues);
    let clonedRightValue = cloneAndModelValue(
      realm,
      rightValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues
    );
    return AbstractValue.createFromBinaryOp(realm, kind, clonedLeftValue, clonedRightValue);
  } else if (
    kind === "!" ||
    kind === "typeof" ||
    kind === "delete" ||
    kind === "+" ||
    kind === "-" ||
    kind === "void" ||
    kind === "~"
  ) {
    invariant(clonableValues.has(val));
    // Unary ops
    let [condValue] = val.args;
    let clonedCondValue = cloneAndModelValue(realm, condValue, funcEffects, knownValues, clonableValues, unknownValues);
    invariant(val.operationDescriptor !== undefined);
    invariant(clonedCondValue instanceof AbstractValue);
    let hasPrefix = val.operationDescriptor.data.prefix;
    return AbstractValue.createFromUnaryOp(realm, kind, clonedCondValue, hasPrefix);
  }

  debugger;
}

function cloneAndModelValue(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Map<Value, string>
): Value {
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, funcEffects, knownValues, clonableValues, unknownValues);
    }
  } else if (val instanceof AbstractValue) {
    return cloneAndModelAbstractValue(realm, val, funcEffects, knownValues, clonableValues, unknownValues);
  }
  invariant(false, "cloneValue was passed an unknown type of cloneValue");
}

export function getModeledValueFromOutlinedFunctionMaker(
  realm: Realm,
  marker: AbstractValue,
  unknownValuesMap?: Map<Value, String>
): Value {
  invariant(marker.kind === "outlined function marker");
  let markerProperties = realm.outlinedFunctionMarkers.get(marker);
  invariant(markerProperties !== undefined);
  let { effects, knownValues, clonableValues, unknownValues } = markerProperties;
  let cloneAndModeledValue;
  let clonedEffects;

  realm.withEffectsAppliedInGlobalEnv(() => {
    let result = effects.result;
    if (result instanceof SimpleNormalCompletion) {
      result = result.value;
    }
    invariant(result instanceof Value);
    let newUnknownValuesMap;
    let intrinsicName;

    if (unknownValuesMap !== undefined) {
      intrinsicName = unknownValuesMap.get(marker);
      newUnknownValuesMap = new Map(unknownValuesMap);
    } else {
      intrinsicName = marker.intrinsicName;
      newUnknownValuesMap = new Map();
    }
    let i = 0;
    for (let value of unknownValues) {
      newUnknownValuesMap.set(value, `${intrinsicName}[${i++}]`);
    }
    clonedEffects = realm.evaluateForEffects(
      () => {
        cloneAndModeledValue = cloneAndModelValue(
          realm,
          result,
          effects,
          knownValues,
          clonableValues,
          newUnknownValuesMap
        );
        return realm.intrinsics.undefined;
      },
      undefined,
      "createAbstractTemporalValue"
    );
    return realm.intrinsics.undefined;
  }, effects);
  realm.applyEffects(clonedEffects);
  return cloneAndModeledValue;
}
