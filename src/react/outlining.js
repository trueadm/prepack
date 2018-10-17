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
  FunctionValue,
  ObjectValue,
  PrimitiveValue,
  StringValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import { PropertyDescriptor, cloneDescriptor } from "../descriptors.js";
import { Get } from "../methods/index.js";
import { Properties, Utils } from "../singletons.js";
import { createOperationDescriptor } from "../utils/generator.js";
import { isReactElement } from "./utils.js";

function getOutliningValuesFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Set<Value>,
  renderValues: Set<Value>
): void {
  if (val instanceof PrimitiveValue) {
    knownValues.add(val);
  } else if (val instanceof ObjectValue) {
    if (!funcEffects.createdObjects.has(val)) {
      knownValues.add(val);
    }
    // These values are key to React component tree optimizations
    if (isReactElement(val) || ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      renderValues.add(val);
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
        collectOutliningValues(realm, propVal, funcEffects, knownValues, clonableValues, unknownValues, renderValues);
      }
    }
    let unknownProperty = val.unknownProperty;
    if (unknownProperty !== undefined) {
      if (unknownProperty.key instanceof Value) {
        collectOutliningValues(
          realm,
          unknownProperty.key,
          funcEffects,
          knownValues,
          clonableValues,
          unknownValues,
          renderValues
        );
      }
      let descriptor = unknownProperty.descriptor;
      if (descriptor !== undefined && descriptor.value instanceof Value) {
        collectOutliningValues(
          realm,
          descriptor.value,
          funcEffects,
          knownValues,
          clonableValues,
          unknownValues,
          renderValues
        );
      }
    }
    if (val instanceof ArrayValue) {
      invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
      clonableValues.add(val);
    } else if (val instanceof FunctionValue) {
      invariant(val.$Prototype === realm.intrinsics.FunctionPrototype);
      // We don't handle cloning functions at this point
      unknownValues.add(val);
    } else if (val.$Prototype === realm.intrinsics.ObjectPrototype) {
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
  renderValues: Set<Value>
): void {
  if (!funcEffects.createdAbstracts.has(val)) {
    knownValues.add(val);
  }
  const kind = val.kind;
  if (kind === "outlined function marker") {
    let markerData = realm.outlinedFunctionMarkerData.get(val);
    invariant(markerData !== undefined);
    let makerRenderValues = markerData.renderValues;
    if (makerRenderValues.size > 0) {
      renderValues.add(val);
    } else {
      unknownValues.add(val);
    }
  } else if (kind === "conditional") {
    clonableValues.add(val);
    let [condValue, consequentVal, alternateVal] = val.args;
    collectOutliningValues(realm, condValue, funcEffects, knownValues, clonableValues, unknownValues, renderValues);
    collectOutliningValues(realm, consequentVal, funcEffects, knownValues, clonableValues, unknownValues, renderValues);
    collectOutliningValues(realm, alternateVal, funcEffects, knownValues, clonableValues, unknownValues, renderValues);
  } else if (val.args.length > 0) {
    clonableValues.add(val);
    for (let arg of val.args) {
      collectOutliningValues(realm, arg, funcEffects, knownValues, clonableValues, unknownValues, renderValues);
    }
  } else if (kind === "widened numeric property") {
    clonableValues.add(val);
  } else if (kind !== undefined && kind.startsWith("property:")) {
    clonableValues.add(val);
  } else if (kind !== undefined && kind.startsWith("template:")) {
    clonableValues.add(val);
  } else if (val.isTemporal() || (kind !== undefined && kind.startsWith("abstractCounted:"))) {
    unknownValues.add(val);
  } else if (val.kind === "mayAliasSet") {
    unknownValues.add(val);
  } else {
    debugger;
  }
}

function collectOutliningValues(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Set<Value>,
  renderValues: Set<Value>
): void {
  if (val instanceof ConcreteValue) {
    return getOutliningValuesFromConcreteValue(
      realm,
      val,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      renderValues
    );
  } else if (val instanceof AbstractValue) {
    return getOutliningValuesFromAbstractValue(
      realm,
      val,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      renderValues
    );
  }
  invariant(false, "unknown value type found in getOutliningValues");
}

export function possiblyOutlineFunctionCall(
  realm: Realm,
  F: FunctionValue,
  thisArgument: Value,
  argsList: Array<Value>,
  originalEffects: Effects
): Value {
  let result = originalEffects.result;
  if (result instanceof AbruptCompletion) {
    debugger;
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    debugger;
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  invariant(result instanceof Value);
  const inlineFunctionCall = () => {
    realm.applyEffects(originalEffects);
    return realm.returnOrThrowCompletion(originalEffects.result);
  };
  let usesThis = thisArgument !== realm.intrinsics.undefined;
  let isPrimitive = result instanceof PrimitiveValue;
  let generator = originalEffects.generator;

  if (
    usesThis ||
    allArgsAreConcreteOrContainsRenderValues(realm, argsList, originalEffects) ||
    isPrimitive ||
    generator._entries.length === 0 ||
    !Utils.areEffectsPure(realm, originalEffects, F)
  ) {
    return inlineFunctionCall();
  }

  let thisValue = realm.intrinsics.undefined;
  let funcToModel = F;
  if (funcToModel instanceof BoundFunctionValue) {
    funcToModel = funcToModel.$BoundTargetFunction;
    thisValue = funcToModel.$BoundThis;
  }
  let funcCall = () => {
    return realm.evaluateFunctionForPureEffects(
      F,
      () => Utils.createModelledFunctionCall(realm, funcToModel, undefined, thisValue)(),
      null,
      "outlining possiblyOutlineFunctionCall",
      () => {
        debugger;
      }
    );
  };

  let effects = realm.isInPureScope() ? funcCall() : realm.evaluateWithPureScope(funcCall);
  result = effects.result;
  if (result instanceof AbruptCompletion) {
    debugger;
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    debugger;
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  let knownValues = new Set();
  let clonableValues = new Set();
  let unknownValues = new Set();
  let renderValues = new Set();

  realm.withEffectsAppliedInGlobalEnv(() => {
    collectOutliningValues(realm, result, effects, knownValues, clonableValues, unknownValues, renderValues);
    return realm.intrinsics.undefined;
  }, effects);

  // realm.collectedNestedOptimizedFunctionEffects.set(F, { effects, thisValue: thisArgument });
  return AbstractValue.createOutlinedFunctionMarker(realm, F, argsList, effects, knownValues, renderValues);
}

function allArgsAreConcreteOrContainsRenderValues(realm: Realm, args: Array<Value>, effects: Effects): boolean {
  for (let arg of args) {
    let knownValues = new Set();
    let clonableValues = new Set();
    let unknownValues = new Set();
    let renderValues = new Set();
    collectOutliningValues(realm, arg, effects, knownValues, clonableValues, unknownValues, renderValues);
    if (renderValues.size > 0) {
      debugger;
      return true;
    }
    if (unknownValues.size > 0) {
      return false;
    }
  }
  return true;
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
  intrinsicName: null | string,
  clonedObject: ObjectValue,
  desc: PropertyDescriptor,
  knownValues: Set<Values>
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, intrinsicName, knownValues);
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
  intrinsicName: null | string,
  knownValues: Set<Values>
): void {
  clonedObject.refuseSerialization = true;
  // TODO do symbols
  for (let [propName, { descriptor }] of val.properties) {
    // TODO support prototypes and callee
    if (propName === "prototype" || propName === "callee") {
      invariant(false, "TODO support prototype and callee");
    }
    invariant(descriptor instanceof PropertyDescriptor);
    let propIntrinsicName = `${intrinsicName}.${propName}`;
    let desc = cloneAndModelObjectPropertyDescriptor(
      realm,
      val,
      propIntrinsicName,
      clonedObject,
      descriptor,
      knownValues
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
        null,
        clonedObject,
        unknownProperty.descriptor,
        knownValues
      );
    }
    if (unknownProperty.key !== undefined) {
      key = cloneAndModelValue(realm, unknownProperty.key, null, knownValues);
    }
    clonedObject.unknownProperty = {
      descriptor: desc,
      key,
      object: clonedObject,
    };
  }
  clonedObject.refuseSerialization = false;
}

function cloneAndModelObjectValue(
  realm: Realm,
  val: ObjectValue,
  intrinsicName: null | string,
  knownValues: Set<Values>
): ObjectValue {
  if (knownValues.has(val)) {
    return val;
  }
  if (val instanceof ArrayValue) {
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    cloneObjectProperties(realm, clonedObject, val, intrinsicName, knownValues);
    applyPostValueConfig(realm, val, clonedObject);
    if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      debugger;
      // if (val.nestedOptimizedFunctionEffects !== undefined) {
      //   clonedObject.nestedOptimizedFunctionEffects = val.nestedOptimizedFunctionEffects;
      // }
      // clonedObject.intrinsicName = unknownValueNameMap.get(val);
      // clonedObject.isScopedTemplate = true;
      // clonedObject.intrinsicNameGenerated = true;
    }
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    invariant(val.$Prototype === realm.intrinsics.FunctionPrototype);
    let abstract = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
    invariant(intrinsicName !== null);
    abstract.intrinsicName = intrinsicName;
    return abstract;
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  cloneObjectProperties(realm, clonedObject, val, intrinsicName, knownValues);
  applyPostValueConfig(realm, val, clonedObject);
  return clonedObject;
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  intrinsicName: null | string,
  knownValues: Set<Values>
): ObjectValue {
  if (knownValues.has(val)) {
    return val;
  }
  const kind = val.kind;
  if (kind === "outlined function marker") {
    // debugger;
  } else if (kind === "conditional") {
    // Conditional ops
    let [condValue, consequentVal, alternateVal] = val.args;
    let clonedCondValue = cloneAndModelValue(realm, condValue, intrinsicName, knownValues);
    let clonedConsequentVal = cloneAndModelValue(realm, consequentVal, intrinsicName, knownValues);
    let clonedAlternateVal = cloneAndModelValue(realm, alternateVal, intrinsicName, knownValues);
    return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
  } else if (kind === "&&" || kind === "||") {
    // Logical ops
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(realm, leftValue, intrinsicName, knownValues);
    let clonedRightValue = cloneAndModelValue(realm, rightValue, intrinsicName, knownValues);
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
    // Binary ops
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(realm, leftValue, intrinsicName, knownValues);
    let clonedRightValue = cloneAndModelValue(realm, rightValue, intrinsicName, knownValues);
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
    // Unary ops
    let [condValue] = val.args;
    let clonedCondValue = cloneAndModelValue(realm, condValue, intrinsicName, knownValues);
    invariant(val.operationDescriptor !== undefined);
    invariant(clonedCondValue instanceof AbstractValue);
    let hasPrefix = val.operationDescriptor.data.prefix;
    return AbstractValue.createFromUnaryOp(realm, kind, clonedCondValue, hasPrefix);
  } else if (kind === "widened numeric property") {
    return AbstractValue.createFromType(realm, Value, "widened numeric property", [...val.args]);
  } else if (kind !== undefined && kind.startsWith("property:")) {
    let clonedArgs = val.args.map(arg => cloneAndModelValue(realm, arg, intrinsicName, knownValues));
    let P = clonedArgs[1];
    invariant(P instanceof StringValue);
    return AbstractValue.createFromBuildFunction(
      realm,
      val.getType(),
      clonedArgs,
      createOperationDescriptor("ABSTRACT_PROPERTY"),
      { kind: AbstractValue.makeKind("property", P.value) }
    );
  } else if (kind !== undefined && kind.startsWith("template:")) {
    let source = kind.replace("template:", "");
    let clonedArgs = val.args.map(arg => cloneAndModelValue(realm, arg, intrinsicName, knownValues));
    return AbstractValue.createFromTemplate(realm, source, val.getType(), clonedArgs);
  } else if (kind === "check for known property") {
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(realm, leftValue, intrinsicName, knownValues);
    let clonedRightValue = cloneAndModelValue(realm, rightValue, intrinsicName, knownValues);
    return AbstractValue.createFromBinaryOp(
      realm,
      "===",
      clonedLeftValue,
      clonedRightValue,
      undefined,
      "check for known property"
    );
  }
  if (val.isTemporal() || (kind !== undefined && kind.startsWith("abstractCounted:"))) {
    let abstract = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
    invariant(intrinsicName !== null);
    abstract.intrinsicName = intrinsicName;
    return abstract;
  }
  debugger;
}

function cloneAndModelValue(realm: Realm, val: Value, intrinsicName: string, knownValues: Set<Values>): Value {
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, intrinsicName, knownValues);
    }
  } else if (val instanceof AbstractValue) {
    return cloneAndModelAbstractValue(realm, val, intrinsicName, knownValues);
  }
  invariant(false, "cloneValue was passed an unknown type of cloneValue");
}

let x = 0;

export function createRenderValuesFromOutlinedFunctionMarker(realm: Realm, marker: AbstractValue): Value {
  invariant(marker.kind === "outlined function marker");
  let markerData = realm.outlinedFunctionMarkerData.get(marker);
  invariant(markerData !== undefined);
  let { effects, knownValues, renderValues, result } = markerData;
  if (renderValues.size === 0) {
    return marker;
  }
  let intrinsicName = marker.intrinsicName;
  // Check if we need to create a conditional to return
  if (result instanceof ConcreteValue) {
    return createModelledValueFromValue(realm, result, intrinsicName, effects, knownValues);
  } else if (result.kind === "outlined function marker") {
    debugger;
  } else {
    debugger;
    // Conditional
    let renderValuesToJoin = Array.from(renderValues);
    intrinsicName = "__REACT_ARR__" + x++;
    return joinRenderValuesAsConditional(realm, intrinsicName, renderValuesToJoin, marker, effects, knownValues);
  }
}

export function createModelledValueFromOutlinedFunctionMarker(realm: Realm, marker: AbstractValue): Value {
  invariant(marker.kind === "outlined function marker");
  let markerData = realm.outlinedFunctionMarkerData.get(marker);
  invariant(markerData !== undefined);
  let { effects, knownValues, result } = markerData;
  let intrinsicName = marker.intrinsicName;
  // Check if we need to create a conditional to return
  if (result instanceof ConcreteValue) {
    return createModelledValueFromValue(realm, result, intrinsicName, effects, knownValues);
  } else {
    debugger;
  }
}

function joinRenderValuesAsConditional(
  realm: Realm,
  intrinsicName: string,
  renderValuesToJoin: Array<Value>,
  marker: AbstractValue,
  effects: Effects,
  knownValues: Set<Value>
): AbstractValue {
  let condition = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
  condition.intrinsicName = "__REACT_VALUE_COND__" + x++;
  let renderValue = renderValuesToJoin.pop();
  if (renderValue instanceof ConcreteValue) {
    renderValue = createModelledValueFromValue(realm, renderValue, intrinsicName, effects, knownValues);
  }
  if (renderValuesToJoin.length === 0) {
    return AbstractValue.createFromConditionalOp(realm, condition, renderValue, marker);
  }
  return AbstractValue.createFromConditionalOp(
    realm,
    condition,
    renderValue,
    joinRenderValuesAsConditional(realm, intrinsicName, renderValuesToJoin, marker, effects, knownValues)
  );
}

function createModelledValueFromValue(
  realm: Realm,
  value: Value,
  intrinsicName: null | string,
  effects: Effects,
  knownValues: Set<Value>
): Value {
  let cloneAndModeledValue;
  let modelledEffects;
  realm.withEffectsAppliedInGlobalEnv(() => {
    modelledEffects = realm.evaluateForEffects(
      () => {
        cloneAndModeledValue = cloneAndModelValue(realm, value, intrinsicName, knownValues);

        return realm.intrinsics.undefined;
      },
      undefined,
      "createAbstractTemporalValue"
    );
    return null;
  }, effects);
  invariant(cloneAndModeledValue instanceof Value);
  realm.applyEffects(modelledEffects);
  return cloneAndModeledValue;
}

// function createModeledValueFromValue(
//   realm: Realm,
//   value: Value,
//   intrinsicName: string,
//   effects: Effects,
//   knownValues: Set<Value>,
//   clonableValues: Set<Value>,
//   unknownValues: Set<Value>
// ): Value {
//   let cloneAndModeledValue;
//   let clonedEffects;

//   realm.withEffectsAppliedInGlobalEnv(() => {
//     let result = effects.result;
//     if (result instanceof SimpleNormalCompletion) {
//       result = result.value;
//     }
//     invariant(result instanceof Value);
//     let unknownValueNameMap = new Map();

//     let i = 0;
//     for (let unknownValue of unknownValues) {
//       unknownValueNameMap.set(unknownValue, `${intrinsicName}[${i++}]`);
//     }
//     clonedEffects = realm.evaluateForEffects(
//       () => {
//         cloneAndModeledValue = cloneAndModelValue(
//           realm,
//           result,
//           effects,
//           knownValues,
//           clonableValues,
//           unknownValueNameMap
//         );
//         return realm.intrinsics.undefined;
//       },
//       undefined,
//       "createAbstractTemporalValue"
//     );
//     return realm.intrinsics.undefined;
//   }, effects);
//   realm.applyEffects(clonedEffects);
//   realm.outlinedFunctionValues.set(value, { effects, knownValues, clonableValues, unknownValues });
//   return cloneAndModeledValue;
// }

// function getModeledValueFromValue(realm: Realm, value: Value, unknownValuesMap: Map<Value, String>): Value {
//   let { effects, knownValues, clonableValues, unknownValues } = realm.outlinedFunctionValues.get(value);
//   let cloneAndModeledValue;
//   let clonedEffects;

//   realm.withEffectsAppliedInGlobalEnv(() => {
//     let result = effects.result;
//     if (result instanceof SimpleNormalCompletion) {
//       result = result.value;
//     }
//     invariant(result instanceof Value);
//     let unknownValueNameMap = new Map(unknownValuesMap);
//     let intrinsicName = unknownValuesMap.get(value);

//     let i = 0;
//     for (let unknownValue of unknownValues) {
//       unknownValueNameMap.set(unknownValue, `${intrinsicName}[${i++}]`);
//     }
//     clonedEffects = realm.evaluateForEffects(
//       () => {
//         cloneAndModeledValue = cloneAndModelValue(
//           realm,
//           result,
//           effects,
//           knownValues,
//           clonableValues,
//           unknownValueNameMap
//         );
//         return realm.intrinsics.undefined;
//       },
//       undefined,
//       "createAbstractTemporalValue"
//     );
//     return realm.intrinsics.undefined;
//   }, effects);
//   realm.applyEffects(clonedEffects);
//   return cloneAndModeledValue;
// }
