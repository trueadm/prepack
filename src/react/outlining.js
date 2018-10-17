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
  ConcreteValue,
  ECMAScriptFunctionValue,
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
  renderValues: Set<Value>,
  isRenderObjectValues?: boolean = false
): void {
  if (val instanceof PrimitiveValue) {
    knownValues.add(val);
  } else if (val instanceof ObjectValue) {
    if (funcEffects.createdObjects.has(val)) {
      unknownValues.add(val);
    } else {
      knownValues.add(val);
    }
    // These values are key to React component tree optimizations
    if (isReactElement(val) || ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      renderValues.add(val);
      isRenderObjectValues = true;
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
        collectOutliningValues(
          realm,
          propVal,
          funcEffects,
          knownValues,
          clonableValues,
          unknownValues,
          renderValues,
          isRenderObjectValues
        );
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
          renderValues,
          isRenderObjectValues
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
          renderValues,
          isRenderObjectValues
        );
      }
    }
    if (val instanceof ArrayValue) {
      invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
      clonableValues.add(val);
    } else if (val instanceof FunctionValue) {
      invariant(val.$Prototype === realm.intrinsics.FunctionPrototype);
      // We don't handle cloning functions at this point
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
  renderValues: Set<Value>,
  isRenderObjectValues?: boolean = false
): void {
  if (funcEffects.createdAbstracts.has(val)) {
    unknownValues.add(val);
  } else {
    knownValues.add(val);
  }
  const kind = val.kind;
  if (kind === "conditional") {
    clonableValues.add(val);
    let [condValue, consequentVal, alternateVal] = val.args;
    collectOutliningValues(
      realm,
      condValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      renderValues,
      isRenderObjectValues
    );
    collectOutliningValues(
      realm,
      consequentVal,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      renderValues,
      isRenderObjectValues
    );
    collectOutliningValues(
      realm,
      alternateVal,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      renderValues,
      isRenderObjectValues
    );
  } else if (val.args.length > 0) {
    clonableValues.add(val);
    for (let arg of val.args) {
      collectOutliningValues(
        realm,
        arg,
        funcEffects,
        knownValues,
        clonableValues,
        unknownValues,
        renderValues,
        isRenderObjectValues
      );
    }
  } else if (kind === "widened numeric property") {
    clonableValues.add(val);
  } else if (kind !== undefined && kind.startsWith("property:")) {
    clonableValues.add(val);
  } else if (kind !== undefined && kind.startsWith("template:")) {
    clonableValues.add(val);
  }
}

function collectOutliningValues(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Set<Value>,
  renderValues: Set<Value>,
  isRenderObjectValues?: boolean = false
): void {
  if (isRenderObjectValues) {
    renderValues.add(val);
  }
  if (val instanceof ConcreteValue) {
    return getOutliningValuesFromConcreteValue(
      realm,
      val,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      renderValues,
      isRenderObjectValues
    );
  } else if (val instanceof AbstractValue) {
    return getOutliningValuesFromAbstractValue(
      realm,
      val,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValues,
      renderValues,
      isRenderObjectValues
    );
  }
  invariant(false, "unknown value type found in getOutliningValues");
}

export function possiblyOutlineFunctionCall(
  realm: Realm,
  F: ECMAScriptFunctionValue,
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
  let allArgsAreConcrete = argsList.every(arg => arg instanceof ConcreteValue);

  if (
    usesThis ||
    allArgsAreConcrete ||
    isPrimitive ||
    generator._entries.length === 0 ||
    !Utils.areEffectsPure(realm, originalEffects, F)
  ) {
    return inlineFunctionCall();
  }
  let knownValues = new Set();
  let clonableValues = new Set();
  let unknownValues = new Set();
  let renderValues = new Set();

  realm.withEffectsAppliedInGlobalEnv(() => {
    collectOutliningValues(realm, result, originalEffects, knownValues, clonableValues, unknownValues, renderValues);
    return realm.intrinsics.undefined;
  }, originalEffects);

  for (let renderValue of renderValues) {
    if (unknownValues.has(renderValue)) {
      return inlineFunctionCall();
    }
  }
  // let funcCall = () => {
  //   return realm.evaluateFunctionForPureEffects(
  //     F,
  //     Utils.createModelledFunctionCall(realm, F, undefined, thisArgument),
  //     null,
  //     "outlining modelAndOptimizeOutlinedFunction",
  //     () => {
  //       debugger;
  //     }
  //   );
  // };

  // let effects = realm.isInPureScope() ? funcCall() : realm.evaluateWithPureScope(funcCall);
  // result = effects.result;
  // if (result instanceof AbruptCompletion) {
  //   debugger;
  // } else if (result instanceof JoinedNormalAndAbruptCompletions) {
  //   debugger;
  // } else if (result instanceof SimpleNormalCompletion) {
  //   result = result.value;
  // }
  // knownValues = new Set();
  // clonableValues = new Set();
  // unknownValues = new Set();
  // renderValues = new Set();

  // realm.withEffectsAppliedInGlobalEnv(() => {
  //   collectOutliningValues(realm, result, effects, knownValues, clonableValues, unknownValues, renderValues);
  //   return realm.intrinsics.undefined;
  // }, effects);


  // realm.collectedNestedOptimizedFunctionEffects.set(F, { effects, thisValue: thisArgument });
  return AbstractValue.createOutlinedFunctionMarker(realm, F, argsList, originalEffects);
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
  desc: PropertyDescriptor,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValueNameMap: Map<Value, string>
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, funcEffects, knownValues, clonableValues, unknownValueNameMap);
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
  unknownValueNameMap: Map<Value, string>
): void {
  clonedObject.refuseSerialization = true;
  // TODO do symbols
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
      descriptor,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
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
        funcEffects,
        knownValues,
        clonableValues,
        unknownValueNameMap
      );
    }
    if (unknownProperty.key !== undefined) {
      key = cloneAndModelValue(
        realm,
        unknownProperty.key,
        funcEffects,
        knownValues,
        clonableValues,
        unknownValueNameMap
      );
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
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValueNameMap: Map<Value, string>
): ObjectValue {
  if (knownValues.has(val)) {
    return val;
  }
  if (val instanceof ArrayValue) {
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    invariant(clonableValues.has(val));
    let clonedObject = new ArrayValue(realm);
    cloneObjectProperties(realm, clonedObject, val, funcEffects, knownValues, clonableValues, unknownValueNameMap);
    applyPostValueConfig(realm, val, clonedObject);
    if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      if (val.nestedOptimizedFunctionEffects !== undefined) {
        clonedObject.nestedOptimizedFunctionEffects = val.nestedOptimizedFunctionEffects;
      }
      clonedObject.intrinsicName = unknownValueNameMap.get(val);
      clonedObject.isScopedTemplate = true;
      clonedObject.intrinsicNameGenerated = true;
    }
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    invariant(val.$Prototype === realm.intrinsics.FunctionPrototype);
    invariant(false, "We should never get here!");
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  invariant(clonableValues.has(val));
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  cloneObjectProperties(realm, clonedObject, val, funcEffects, knownValues, clonableValues, unknownValueNameMap);
  applyPostValueConfig(realm, val, clonedObject);
  return clonedObject;
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValueNameMap: Map<Value, string>
): ObjectValue {
  if (knownValues.has(val)) {
    return val;
  }
  const kind = val.kind;
  if (kind === "conditional") {
    invariant(clonableValues.has(val));
    // Conditional ops
    let [condValue, consequentVal, alternateVal] = val.args;
    let clonedCondValue = cloneAndModelValue(
      realm,
      condValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
    );
    let clonedConsequentVal = cloneAndModelValue(
      realm,
      consequentVal,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
    );
    let clonedAlternateVal = cloneAndModelValue(
      realm,
      alternateVal,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
    );
    return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
  } else if (kind === "&&" || kind === "||") {
    invariant(clonableValues.has(val));
    // Logical ops
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(
      realm,
      leftValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
    );
    let clonedRightValue = cloneAndModelValue(
      realm,
      rightValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
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
    let clonedLeftValue = cloneAndModelValue(
      realm,
      leftValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
    );
    let clonedRightValue = cloneAndModelValue(
      realm,
      rightValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
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
    let clonedCondValue = cloneAndModelValue(
      realm,
      condValue,
      funcEffects,
      knownValues,
      clonableValues,
      unknownValueNameMap
    );
    invariant(val.operationDescriptor !== undefined);
    invariant(clonedCondValue instanceof AbstractValue);
    let hasPrefix = val.operationDescriptor.data.prefix;
    return AbstractValue.createFromUnaryOp(realm, kind, clonedCondValue, hasPrefix);
  } else if (kind === "widened numeric property") {
    return AbstractValue.createFromType(realm, Value, "widened numeric property", [...val.args]);
  } else if (kind !== undefined && kind.startsWith("property:")) {
    let clonedArgs = val.args.map(arg =>
      cloneAndModelValue(realm, arg, funcEffects, knownValues, clonableValues, unknownValueNameMap)
    );
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
    let clonedArgs = val.args.map(arg =>
      cloneAndModelValue(realm, arg, funcEffects, knownValues, clonableValues, unknownValueNameMap)
    );
    return AbstractValue.createFromTemplate(realm, source, val.getType(), clonedArgs);
  }

  debugger;
}

function cloneAndModelValue(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValueNameMap: Map<Value, string>
): Value {
  if (realm.outlinedFunctionValues.has(val)) {
    debugger;
  }
  if (unknownValueNameMap.has(val) && !clonableValues.has(val)) {
    let intrinsicName = unknownValueNameMap.get(val);
    let clonedAbstractValue = AbstractValue.createFromType(realm, val.getType(), "outlined abstract intrinsic", []);
    clonedAbstractValue.intrinsicName = intrinsicName;
    return clonedAbstractValue;
  }
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, funcEffects, knownValues, clonableValues, unknownValueNameMap);
    }
  } else if (val instanceof AbstractValue) {
    return cloneAndModelAbstractValue(realm, val, funcEffects, knownValues, clonableValues, unknownValueNameMap);
  }
  invariant(false, "cloneValue was passed an unknown type of cloneValue");
}

function createModeledValueFromValue(
  realm: Realm,
  value: Value,
  intrinsicName: string,
  effects: Effects,
  knownValues: Set<Value>,
  clonableValues: Set<Value>,
  unknownValues: Set<Value>
): Value {
  let cloneAndModeledValue;
  let clonedEffects;

  realm.withEffectsAppliedInGlobalEnv(() => {
    let result = effects.result;
    if (result instanceof SimpleNormalCompletion) {
      result = result.value;
    }
    invariant(result instanceof Value);
    let unknownValueNameMap = new Map();

    let i = 0;
    for (let unknownValue of unknownValues) {
      unknownValueNameMap.set(unknownValue, `${intrinsicName}[${i++}]`);
    }
    clonedEffects = realm.evaluateForEffects(
      () => {
        cloneAndModeledValue = cloneAndModelValue(
          realm,
          result,
          effects,
          knownValues,
          clonableValues,
          unknownValueNameMap
        );
        return realm.intrinsics.undefined;
      },
      undefined,
      "createAbstractTemporalValue"
    );
    return realm.intrinsics.undefined;
  }, effects);
  realm.applyEffects(clonedEffects);
  realm.outlinedFunctionValues.set(value, { effects, knownValues, clonableValues, unknownValues });
  return cloneAndModeledValue;
}

function getModeledValueFromValue(realm: Realm, value: Value, unknownValuesMap: Map<Value, String>): Value {
  let { effects, knownValues, clonableValues, unknownValues } = realm.outlinedFunctionValues.get(value);
  let cloneAndModeledValue;
  let clonedEffects;

  realm.withEffectsAppliedInGlobalEnv(() => {
    let result = effects.result;
    if (result instanceof SimpleNormalCompletion) {
      result = result.value;
    }
    invariant(result instanceof Value);
    let unknownValueNameMap = new Map(unknownValuesMap);
    let intrinsicName = unknownValuesMap.get(value);

    let i = 0;
    for (let unknownValue of unknownValues) {
      unknownValueNameMap.set(unknownValue, `${intrinsicName}[${i++}]`);
    }
    clonedEffects = realm.evaluateForEffects(
      () => {
        cloneAndModeledValue = cloneAndModelValue(
          realm,
          result,
          effects,
          knownValues,
          clonableValues,
          unknownValueNameMap
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
