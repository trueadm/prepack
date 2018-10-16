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
import { AbstractValue, ECMAScriptFunctionValue, PrimitiveValue, Value } from "../values/index.js";
import invariant from "../invariant.js";
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import { InternalCall } from "./function.js";
import { Utils } from "../singletons.js";
import { createOperationDescriptor } from "../utils/generator.js";

export function PossiblyOutlineInternalFunctionCall(
  realm: Realm,
  F: ECMAScriptFunctionValue,
  thisArgument: Value,
  argsList: Array<Value>
): Value {
  let savedOptimizedFunctions = new Set(realm.optimizedFunctions);
  let effects = realm.evaluateForEffects(
    () => InternalCall(realm, F, thisArgument, argsList, 0),
    null,
    "possiblePureFuncCall $Call"
  );
  let result = effects.result;
  if (result instanceof AbruptCompletion) {
    realm.applyEffects(effects);
    throw result;
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    // TODO we should support outlining JoinedNormalAndAbruptCompletions at some point
    return InternalCall(realm, F, thisArgument, argsList, 0);
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  invariant(result instanceof Value);
  const inlineFunctionCall = () => {
    realm.applyEffects(effects);
    return result;
  };
  let usesThis = thisArgument !== realm.intrinsics.undefined;
  let functionContainedOptimizeCalls = realm.optimizedFunctions.size !== savedOptimizedFunctions.size;
  let isPrimitive = result instanceof PrimitiveValue;

  if (functionContainedOptimizeCalls || isPrimitive || usesThis || !Utils.areEffectsPure(realm, effects, F)) {
    return inlineFunctionCall();
  }
  let body = F.$ECMAScriptCode.body;
  if (body.length < 4) {
    return inlineFunctionCall();
  }
  debugger;
  return AbstractValue.createTemporalFromBuildFunction(
    realm,
    result.getType(),
    [F, ...argsList],
    createOperationDescriptor("OUTLINE_FUNCTION_CALL"),
    // TODO: isPure isn't strictly correct here, as the function
    // might contain abstract function calls that we need to happen
    // and won't happen if the temporal is never referenced (thus DCE).
    { isPure: true }
  );
}
