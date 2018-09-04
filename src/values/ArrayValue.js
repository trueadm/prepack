/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow strict-local */

import type { Effects, Realm } from "../realm.js";
import type { PropertyKeyValue, Descriptor, ObjectKind } from "../types.js";
import {
  AbstractValue,
  BoundFunctionValue,
  ECMAScriptSourceFunctionValue,
  NumberValue,
  ObjectValue,
  StringValue,
  Value,
} from "./index.js";
import { IsAccessorDescriptor, IsPropertyKey, IsArrayIndex } from "../methods/is.js";
import { Leak, Materialize, Properties, To, Utils } from "../singletons.js";
import { type OperationDescriptor } from "../utils/generator.js";
import invariant from "../invariant.js";
import { NestedOptimizedFunctionSideEffect } from "../errors.js";
import { PropertyDescriptor } from "../descriptors.js";

type PossibleNestedOptimizedFunctions = [
  { func: BoundFunctionValue | ECMAScriptSourceFunctionValue, thisValue: Value },
];

function evaluatePossibleNestedOptimizedFunctionsAndStoreEffects(
  realm: Realm,
  abstractArrayValue: ArrayValue,
  possibleNestedOptimizedFunctions: PossibleNestedOptimizedFunctions
): void {
  for (let { func, thisValue } of possibleNestedOptimizedFunctions) {
    let funcToModel = func;
    if (func instanceof BoundFunctionValue) {
      funcToModel = func.$BoundTargetFunction;
      thisValue = func.$BoundThis;
    }
    invariant(funcToModel instanceof ECMAScriptSourceFunctionValue);
    let funcCall = Utils.createModelledFunctionCall(realm, funcToModel, undefined, thisValue);
    // We take the modelled function and wrap it in a pure evaluation so we can check for
    // side-effects that occur when evaluating the function. If there are side-effects, then
    // we don't try and optimize the nested function.
    let pureFuncCall = () =>
      realm.evaluatePure(funcCall, /*bubbles*/ false, () => {
        throw new NestedOptimizedFunctionSideEffect();
      });
    let effects;
    try {
      effects = realm.evaluateForEffects(pureFuncCall, null, "temporalArray nestedOptimizedFunction");
    } catch (e) {
      // If the nested optimized function had side-effects, we need to fallback to
      // the default behaviour and leaked the nested functions so any bindings
      // within the function properly leak and materialize.
      if (e instanceof NestedOptimizedFunctionSideEffect) {
        Leak.value(realm, func);
        return;
      }
      throw e;
    }

    // This is an incremental step from this list aimed to resolve a particular issue: #2452
    //
    // Assumptions:
    // 1. We are here because the array op is pure, havocing of bindings is not needed.
    // 2. The array op is only used once. To be enforced: #2448
    // 3. Aliasing effects will lead to a fatal error. To be enforced: #2449
    // 4. Indices of a widened array are not backed by locations
    //
    // Transitive materialization is needed to unblock this issue: #2405
    //
    // The bindings themselves do not have to materialize, since the values in them
    // are used to optimize the nested optimized function. We compute the set of
    // objects that are transitively reachable from read bindings and materialize them.

    Materialize.materializeObjectsTransitive(realm, func);

    // We assume that we do not have to materialize widened arrays because they are intrinsic.
    // If somebody changes the underlying design in a major way, then materialization could be
    // needed, and this check will fail.
    invariant(abstractArrayValue.isIntrinsic());

    // Check if effects were pure then add them
    if (abstractArrayValue.nestedOptimizedFunctionEffects === undefined) {
      abstractArrayValue.nestedOptimizedFunctionEffects = new Map();
    }
    abstractArrayValue.nestedOptimizedFunctionEffects.set(funcToModel, effects);
    realm.collectedNestedOptimizedFunctionEffects.set(funcToModel, effects);
  }
}

function createArrayWithWidenedNumericProperty(
  realm: Realm,
  intrinsicName: string,
  possibleNestedOptimizedFunctions?: PossibleNestedOptimizedFunctions
): ArrayValue {
  let abstractArrayValue = new ArrayValue(realm, intrinsicName);

  if (possibleNestedOptimizedFunctions !== undefined) {
    if (realm.arrayNestedOptimizedFunctionsEnabled && (!realm.react.enabled || realm.react.optimizeNestedFunctions)) {
      evaluatePossibleNestedOptimizedFunctionsAndStoreEffects(
        realm,
        abstractArrayValue,
        possibleNestedOptimizedFunctions
      );
    } else {
      // If nested optimized functions are disabled, we need to fallback to
      // the default behaviour and leaked the nested functions so any bindings
      // within the function properly leak and materialize.
      for (let { func } of possibleNestedOptimizedFunctions) {
        Leak.value(realm, func);
      }
    }
  }
  // Add unknownProperty so we manually handle this object property access
  abstractArrayValue.unknownProperty = {
    key: undefined,
    descriptor: new PropertyDescriptor({
      value: AbstractValue.createFromType(realm, Value, "widened numeric property"),
    }),
    object: abstractArrayValue,
  };
  return abstractArrayValue;
}

export default class ArrayValue extends ObjectValue {
  constructor(realm: Realm, intrinsicName?: string) {
    super(realm, realm.intrinsics.ArrayPrototype, intrinsicName);
  }
  nestedOptimizedFunctionEffects: void | Map<ECMAScriptSourceFunctionValue, Effects>;

  getKind(): ObjectKind {
    return "Array";
  }

  isSimpleObject(): boolean {
    return this.$TypedArrayName === undefined;
  }

  // ECMA262 9.4.2.1
  $DefineOwnProperty(P: PropertyKeyValue, Desc: Descriptor): boolean {
    let A = this;

    // 1. Assert: IsPropertyKey(P) is true.
    invariant(IsPropertyKey(this.$Realm, P), "expected a property key");

    // 2. If P is "length", then
    if (P === "length" || (P instanceof StringValue && P.value === "length")) {
      // a. Return ? ArraySetLength(A, Desc).
      return Properties.ArraySetLength(this.$Realm, A, Desc);
    } else if (IsArrayIndex(this.$Realm, P)) {
      if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(this)) {
        // The length of an array with widenend numeric properties is always abstract
        let succeeded = Properties.OrdinaryDefineOwnProperty(this.$Realm, A, P, Desc);
        if (succeeded === false) return false;
        return true;
      }
      // 3. Else if P is an array index, then

      // a. Let oldLenDesc be OrdinaryGetOwnProperty(A, "length").
      let oldLenDesc = Properties.OrdinaryGetOwnProperty(this.$Realm, A, "length");

      // b. Assert: oldLenDesc will never be undefined or an accessor descriptor because Array objects are
      //    created with a length data property that cannot be deleted or reconfigured.
      invariant(
        oldLenDesc !== undefined && !IsAccessorDescriptor(this.$Realm, oldLenDesc),
        "cannot be undefined or an accessor descriptor"
      );
      Properties.ThrowIfMightHaveBeenDeleted(oldLenDesc);
      oldLenDesc = oldLenDesc.throwIfNotConcrete(this.$Realm);

      // c. Let oldLen be oldLenDesc.[[Value]].
      let oldLen = oldLenDesc.value;
      invariant(oldLen instanceof Value);
      oldLen = oldLen.throwIfNotConcrete();
      invariant(oldLen instanceof NumberValue, "expected number value");
      oldLen = oldLen.value;

      // d. Let index be ! ToUint32(P).
      let index = To.ToUint32(this.$Realm, typeof P === "string" ? new StringValue(this.$Realm, P) : P);

      // e. If index ≥ oldLen and oldLenDesc.[[Writable]] is false, return false.
      if (index >= oldLen && oldLenDesc.writable === false) return false;

      // f. Let succeeded be ! OrdinaryDefineOwnProperty(A, P, Desc).
      let succeeded = Properties.OrdinaryDefineOwnProperty(this.$Realm, A, P, Desc);

      // g. If succeeded is false, return false.
      if (succeeded === false) return false;

      // h. If index ≥ oldLen, then
      if (index >= oldLen) {
        // i. Set oldLenDesc.[[Value]] to index + 1.
        oldLenDesc.value = new NumberValue(this.$Realm, index + 1);

        // ii. Let succeeded be OrdinaryDefineOwnProperty(A, "length", oldLenDesc).
        succeeded = Properties.OrdinaryDefineOwnProperty(this.$Realm, A, "length", oldLenDesc);

        // iii. Assert: succeeded is true.
        invariant(succeeded, "expected length definition to succeed");
      }

      // i. Return true.
      return true;
    }

    // 1. Return OrdinaryDefineOwnProperty(A, P, Desc).
    return Properties.OrdinaryDefineOwnProperty(this.$Realm, A, P, Desc);
  }

  static createTemporalWithWidenedNumericProperty(
    realm: Realm,
    args: Array<Value>,
    operationDescriptor: OperationDescriptor,
    possibleNestedOptimizedFunctions?: PossibleNestedOptimizedFunctions
  ): ArrayValue {
    invariant(realm.generator !== undefined);
    let value = realm.generator.deriveConcreteObject(
      intrinsicName => createArrayWithWidenedNumericProperty(realm, intrinsicName, possibleNestedOptimizedFunctions),
      args,
      operationDescriptor,
      { isPure: true }
    );
    invariant(value instanceof ArrayValue);
    return value;
  }

  static isIntrinsicAndHasWidenedNumericProperty(obj: Value): boolean {
    if (obj instanceof ArrayValue && obj.intrinsicName !== undefined) {
      const prop = obj.unknownProperty;
      if (prop !== undefined && prop.descriptor !== undefined) {
        const desc = prop.descriptor.throwIfNotConcrete(obj.$Realm);
        return desc.value instanceof AbstractValue && desc.value.kind === "widened numeric property";
      }
    }
    return false;
  }
}
