/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { type Realm, Effects } from "../realm.js";
import { AbstractValue, ConcreteValue, FunctionValue, NativeFunctionValue, Value } from "../values/index.js";
import { AbruptCompletion, Completion, PossiblyNormalCompletion } from "../completions.js";
import invariant from "../invariant.js";
import * as t from "babel-types";
import { Havoc } from "../singletons.js";

export type MembraneState = {
  analyzeStage: boolean,
  directFunctionCall: Map<FunctionValue, Array<DirectFunctionCallEntry>>,
};

type DirectFunctionCallEntry = {
  failed: boolean,
  returnValue: void | Value,
};

function createMembraneState(): MembraneState {
  return {
    analyzeStage: true,
    directFunctionCall: new Map(),
  };
}

function createCallExpressionEntry(failed: boolean, returnValue: void | Value): DirectFunctionCallEntry {
  return {
    failed,
    returnValue,
  };
}

function applyEffects(realm: Realm, effects: Effects): Value | Completion {
  // Note that the effects of (non joining) abrupt branches are not included
  // in effects, but are tracked separately inside completion.
  realm.applyEffects(effects);
  let completion = effects.result;
  if (completion instanceof PossiblyNormalCompletion) {
    // in this case one of the branches may complete abruptly, which means that
    // not all control flow branches join into one flow at this point.
    // Consequently we have to continue tracking changes until the point where
    // all the branches come together into one.
    completion = realm.composeWithSavedCompletion(completion);
  }
  // return or throw completion
  if (completion instanceof AbruptCompletion) throw completion;
  invariant(completion instanceof Value);
  return completion;
}

// This requires 1.21 gigawatts of power to work
export class MembraneImplementation {
  analyzeAndOptimizeFunctionCalls(
    realm: Realm,
    original: () => Value,
    generatorName: string,
    restStateFunc?: () => void
  ): Effects {
    if (!realm.membraneEnabled) {
      return realm.evaluateForEffectsInGlobalEnv(original, undefined, generatorName);
    }
    let membraneState = createMembraneState();
    realm.membraneState = membraneState;
    try {
      // analyze phase
      realm.evaluateForEffectsInGlobalEnv(original, undefined, generatorName);
      membraneState.analyzeStage = false;
      if (restStateFunc) {
        restStateFunc();
      }
      // optimize phase
      return realm.evaluateForEffectsInGlobalEnv(original, undefined, generatorName);
    } finally {
      realm.membraneState = undefined;
    }
  }

  EvaluateDirectCall(
    realm: Realm,
    func: Value,
    argumentList: Array<Value>,
    thisValue: Value,
    original: () => Value
  ): Value {
    return original();
    if (
      !realm.membraneEnabled ||
      realm.membraneState === undefined ||
      func instanceof NativeFunctionValue ||
      !(func instanceof FunctionValue)
    ) {
      return original();
    }
    let { analyzeStage, directFunctionCall } = realm.membraneState;
    let directFunctionCallEntries;
    if (!directFunctionCall.has(func)) {
      directFunctionCallEntries = [];
      directFunctionCall.set(func, directFunctionCallEntries);
    } else {
      directFunctionCallEntries = directFunctionCall.get(func);
      invariant(directFunctionCallEntries !== undefined);
    }
    let effects;
    try {
      effects = realm.evaluateForEffects(original, undefined, "Membrane.EvaluateDirectCall");
    } catch (e) {
      if (analyzeStage) {
        directFunctionCallEntries.push(createCallExpressionEntry(true));
      }
      throw e;
    }
    if (analyzeStage) {
      let result = applyEffects(realm, effects);
      invariant(result instanceof Value);
      directFunctionCallEntries.push(createCallExpressionEntry(false, result));
      return result;
    } else {
      // At this point we determine if we want leave the function call in place.
      // For now we only leave it in place if the return value was concrete and
      // the effects has more than 4 generator entries.
      let { result, generator } = effects;
      if (result instanceof ConcreteValue && generator._entries.length > 4) {
        let args = [func, ...argumentList];
        let functionIsPure = false;

        // First we check that the effects were pure and didn't mutate anything
        // outside what it created, includig on what we pass it.
        if (functionIsPure) {
          for (let arg of args) {
            if (arg !== func) {
              Havoc.value(realm, arg);
            }
          }
        } else {
          // If not, we havoc all the bindings passed to the function and the function itsemf
          AbstractValue.createTemporalFromBuildFunction(realm, Value, args, ([funcNode, ...callArgs]) => {
            return t.callExpression(funcNode, ((callArgs: any): Array<any>));
          });
        }
        return result;
      }
      let value = applyEffects(realm, effects);
      invariant(value instanceof Value);
      return value;
    }
  }
}
