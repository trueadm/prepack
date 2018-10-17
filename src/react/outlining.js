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
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import { Get } from "../methods/index.js";
import { Properties, Utils } from "../singletons.js";
import { isReactElement } from "./utils.js";
import { cloneDescriptor, PropertyDescriptor } from "../descriptors.js";

function shouldInlineConcreteValue(realm: Realm, val: ConcreteValue, funcEffects: Effects): void {
  if (val instanceof PrimitiveValue) {
    return false;
  } else if (val instanceof ObjectValue) {
    if (!funcEffects.createdObjects.has(val)) {
      return false;
    }
    // These values are key to React component tree optimizations
    if (isReactElement(val) || ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      return true;
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
        let shouldInline = shouldInlineValue(realm, propVal, funcEffects);
        if (shouldInline) {
          return true;
        }
      }
    }
  }
  return false;
}

function shouldInlineAbstractValue(realm: Realm, val: AbstractValue, funcEffects: Effects): void {
  if (!funcEffects.createdAbstracts.has(val)) {
    return false;
  }
  if (val.args.length > 0) {
    for (let arg of val.args) {
      let shouldInline = shouldInlineValue(realm, arg, funcEffects);
      if (shouldInline) {
        return true;
      }
    }
  }
  return false;
}

function shouldInlineValue(realm: Realm, val: Value, funcEffects: Effects): void {
  if (val instanceof ConcreteValue) {
    return shouldInlineConcreteValue(realm, val, funcEffects);
  } else if (val instanceof AbstractValue) {
    return shouldInlineAbstractValue(realm, val, funcEffects);
  }
  invariant(false, "unknown value type found in getOutliningValues");
}

function shouldCloneConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  funcEffects: Effects,
  skipUnknownAbstractProperties: boolean
): void {
  if (val instanceof PrimitiveValue) {
    return true;
  } else if (val instanceof ObjectValue) {
    if (!funcEffects.createdObjects.has(val)) {
      return true;
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
        let shouldClone = shouldCloneValue(realm, propVal, funcEffects, skipUnknownAbstractProperties);
        if (!shouldClone) {
          if (propVal instanceof AbstractValue && skipUnknownAbstractProperties) {
            return true;
          }
          return false;
        }
      }
    }
    if (val instanceof FunctionValue) {
      return false;
    }
  }
  return true;
}

function shouldCloneAbstractValue(
  realm: Realm,
  val: AbstractValue,
  funcEffects: Effects,
  skipUnknownAbstractProperties: boolean
): void {
  if (!funcEffects.createdAbstracts.has(val)) {
    return true;
  }
  if (val.args.length > 0) {
    for (let arg of val.args) {
      let shouldClone = shouldCloneValue(realm, arg, funcEffects, skipUnknownAbstractProperties);
      if (!shouldClone) {
        return false;
      }
    }
    return true;
  }
  if (val.isTemporal() || val.kind === "outlined abstract intrinsic") {
    return false;
  }
  debugger;
  return false;
}

function shouldCloneValue(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  skipUnknownAbstractProperties: boolean
): void {
  if (val instanceof ConcreteValue) {
    return shouldCloneConcreteValue(realm, val, funcEffects, skipUnknownAbstractProperties);
  } else if (val instanceof AbstractValue) {
    return shouldCloneAbstractValue(realm, val, funcEffects, skipUnknownAbstractProperties);
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
  let isPrimitive = result instanceof PrimitiveValue;
  let generator = originalEffects.generator;

  if (isPrimitive || generator._entries.length < 3 || !Utils.areEffectsPure(realm, originalEffects, F)) {
    return inlineFunctionCall();
  }
  let shouldInline = false;
  let shouldClone = false;

  realm.withEffectsAppliedInGlobalEnv(() => {
    shouldInline = shouldInlineValue(realm, result, originalEffects);
    shouldClone = shouldCloneValue(realm, result, originalEffects, true);
    return realm.intrinsics.undefined;
  }, originalEffects);

  if (shouldInline) {
    return inlineFunctionCall();
  }
  let marker = AbstractValue.createOutlinedFunctionMarker(realm, F, argsList, originalEffects);

  if (shouldClone) {
    return createModelledValueFromValue(realm, result, marker.intrinsicName, originalEffects);
  }

  return marker;
}

function applyPostValueConfig(realm: Realm, value: Value, clonedValue: Value, intrinsicName: string): void {
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
    value.isScopedTemplate = true;
    value.intrinsicNameGenerated = true;
  }
  value.intrinsicName = intrinsicName;
}

function cloneAndModelObjectPropertyDescriptor(
  realm: Realm,
  object: ObjectValue,
  intrinsicName: null | string,
  clonedObject: ObjectValue,
  desc: PropertyDescriptor,
  effects: Effects
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, intrinsicName, effects);
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
  effects: Effects
): void {
  clonedObject.refuseSerialization = true;
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
    let propIntrinsicName = `${intrinsicName}.${propName}`;
    let desc = cloneAndModelObjectPropertyDescriptor(realm, val, propIntrinsicName, clonedObject, descriptor, effects);
    Properties.OrdinaryDefineOwnProperty(realm, clonedObject, propName, desc);
  }
  let unknownProperty = val.unknownProperty;
  if (unknownProperty !== undefined) {
    let desc;
    let key;
    if (unknownProperty.descriptor !== undefined) {
      desc = cloneAndModelObjectPropertyDescriptor(realm, val, null, clonedObject, unknownProperty.descriptor, effects);
    }
    if (unknownProperty.key !== undefined) {
      key = cloneAndModelValue(realm, unknownProperty.key, null, effects);
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
  effects: Effects
): ObjectValue {
  if (!effects.createdObjects.has(val)) {
    return val;
  }
  if (val instanceof ArrayValue) {
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    cloneObjectProperties(realm, clonedObject, val, intrinsicName, effects);
    applyPostValueConfig(realm, val, clonedObject, intrinsicName);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    let abstract = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
    invariant(intrinsicName !== null);
    abstract.intrinsicName = intrinsicName;
    return abstract;
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  cloneObjectProperties(realm, clonedObject, val, intrinsicName, effects);
  applyPostValueConfig(realm, val, clonedObject, intrinsicName);
  return clonedObject;
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  intrinsicName: null | string,
  effects: Effects
): ObjectValue {
  if (!effects.createdAbstracts.has(val)) {
    return val;
  }
  let abstract = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
  invariant(intrinsicName !== null);
  abstract.intrinsicName = intrinsicName;
  return abstract;
}

function cloneAndModelValue(realm: Realm, val: Value, intrinsicName: string, effects: Effects): Value {
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, intrinsicName, effects);
    }
  } else if (val instanceof AbstractValue) {
    return cloneAndModelAbstractValue(realm, val, intrinsicName, effects);
  }
  invariant(false, "cloneValue was passed an unknown type of cloneValue");
}

function createModelledValueFromValue(
  realm: Realm,
  value: Value,
  intrinsicName: null | string,
  effects: Effects
): Value {
  let cloneAndModeledValue;
  let modelledEffects;
  realm.withEffectsAppliedInGlobalEnv(() => {
    modelledEffects = realm.evaluateForEffects(
      () => {
        cloneAndModeledValue = cloneAndModelValue(realm, value, intrinsicName, effects);

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
