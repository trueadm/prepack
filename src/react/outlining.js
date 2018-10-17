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
import { Utils } from "../singletons.js";
import { isReactElement } from "./utils.js";

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
  if (val.isTemporal()) {
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
  let usesThis = thisArgument !== realm.intrinsics.undefined;
  let isPrimitive = result instanceof PrimitiveValue;
  let generator = originalEffects.generator;

  if (isPrimitive || generator._entries.length === 0 || !Utils.areEffectsPure(realm, originalEffects, F)) {
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
  if (shouldClone) {
    debugger;
  }

  return AbstractValue.createOutlinedFunctionMarker(realm, F, argsList, originalEffects);
}
