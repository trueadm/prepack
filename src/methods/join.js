/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { Binding } from "../environment.js";
import { FatalError } from "../errors.js";
import type {
  Bindings,
  BindingEntry,
  Effects,
  EvaluationResult,
  PropertyBindings,
  CreatedObjects,
  Realm,
} from "../realm.js";
import type { Descriptor, PropertyBinding } from "../types.js";

import {
  AbruptCompletion,
  BreakCompletion,
  Completion,
  ContinueCompletion,
  PossiblyNormalCompletion,
  JoinedAbruptCompletions,
  NormalCompletion,
  ReturnCompletion,
  ThrowCompletion,
} from "../completions.js";
import { Reference } from "../environment.js";
import { cloneDescriptor, equalDescriptors, IsDataDescriptor, StrictEqualityComparison } from "../methods/index.js";
import { construct_empty_effects } from "../realm.js";
import { Generator } from "../utils/generator.js";
import { AbstractValue, ObjectValue, Value } from "../values/index.js";

import invariant from "../invariant.js";

function joinGenerators(
  realm: Realm,
  joinCondition: AbstractValue,
  generator1: Generator,
  generator2: Generator
): Generator {
  let result = new Generator(realm);
  if (!generator1.empty() || !generator2.empty()) {
    result.joinGenerators(joinCondition, generator1, generator2);
  }
  return result;
}

function joinArrays(
  realm: Realm,
  v1: void | Array<Value> | Array<{ $Key: void | Value, $Value: void | Value }>,
  v2: void | Array<Value> | Array<{ $Key: void | Value, $Value: void | Value }>,
  getAbstractValue: (void | Value, void | Value) => Value
): Array<Value> | Array<{ $Key: void | Value, $Value: void | Value }> {
  let e = (v1 && v1[0]) || (v2 && v2[0]);
  if (e instanceof Value) return joinArraysOfValues(realm, (v1: any), (v2: any), getAbstractValue);
  else return joinArrayOfsMapEntries(realm, (v1: any), (v2: any), getAbstractValue);
}

function joinArrayOfsMapEntries(
  realm: Realm,
  a1: void | Array<{ $Key: void | Value, $Value: void | Value }>,
  a2: void | Array<{ $Key: void | Value, $Value: void | Value }>,
  getAbstractValue: (void | Value, void | Value) => Value
): Array<{ $Key: void | Value, $Value: void | Value }> {
  let empty = realm.intrinsics.empty;
  let n = Math.max((a1 && a1.length) || 0, (a2 && a2.length) || 0);
  let result = [];
  for (let i = 0; i < n; i++) {
    let { $Key: key1, $Value: val1 } = (a1 && a1[i]) || { $Key: empty, $Value: empty };
    let { $Key: key2, $Value: val2 } = (a2 && a2[i]) || { $Key: empty, $Value: empty };
    if (key1 === undefined && key2 === undefined) {
      result[i] = { $Key: undefined, $Value: undefined };
    } else {
      let key3 = getAbstractValue(key1, key2);
      let val3 = getAbstractValue(val1, val2);
      result[i] = { $Key: key3, $Value: val3 };
    }
  }
  return result;
}

function joinArraysOfValues(
  realm: Realm,
  a1: void | Array<Value>,
  a2: void | Array<Value>,
  getAbstractValue: (void | Value, void | Value) => Value
): Array<Value> {
  let n = Math.max((a1 && a1.length) || 0, (a2 && a2.length) || 0);
  let result = [];
  for (let i = 0; i < n; i++) {
    result[i] = getAbstractValue((a1 && a1[i]) || undefined, (a2 && a2[i]) || undefined);
  }
  return result;
}

export class JoinImplementation {
  stopEffectCaptureJoinApplyAndReturnCompletion(
    c1: PossiblyNormalCompletion,
    c2: AbruptCompletion,
    realm: Realm
  ): AbruptCompletion {
    let e = realm.getCapturedEffects(c1);
    invariant(e !== undefined);
    realm.stopEffectCaptureAndUndoEffects(c1);
    let joined_effects = this.joinPossiblyNormalCompletionWithAbruptCompletion(realm, c1, c2, e);
    realm.applyEffects(joined_effects);
    let result = joined_effects[0];
    invariant(result instanceof AbruptCompletion);
    return result;
  }

  unbundleNormalCompletion(
    completionOrValue: Completion | Value | Reference
  ): [void | NormalCompletion, Value | Reference] {
    let completion, value;
    if (completionOrValue instanceof PossiblyNormalCompletion) {
      completion = completionOrValue;
      value = completionOrValue.value;
    } else {
      invariant(completionOrValue instanceof Value || completionOrValue instanceof Reference);
      value = completionOrValue;
    }
    return [completion, value];
  }

  composeNormalCompletions(
    leftCompletion: void | NormalCompletion,
    rightCompletion: void | NormalCompletion,
    resultValue: Value,
    realm: Realm
  ): PossiblyNormalCompletion | Value {
    if (leftCompletion instanceof PossiblyNormalCompletion) {
      if (rightCompletion instanceof PossiblyNormalCompletion) {
        this.updatePossiblyNormalCompletionWithValue(realm, rightCompletion, resultValue);
        return this.composePossiblyNormalCompletions(realm, leftCompletion, rightCompletion);
      }
      this.updatePossiblyNormalCompletionWithValue(realm, leftCompletion, resultValue);
      return leftCompletion;
    } else if (rightCompletion instanceof PossiblyNormalCompletion) {
      this.updatePossiblyNormalCompletionWithValue(realm, rightCompletion, resultValue);
      return rightCompletion;
    } else {
      invariant(leftCompletion === undefined && rightCompletion === undefined);
      return resultValue;
    }
  }

  composePossiblyNormalCompletions(
    realm: Realm,
    pnc: PossiblyNormalCompletion,
    c: PossiblyNormalCompletion
  ): PossiblyNormalCompletion {
    //merge the two pathConditions
    let composedPath = [];
    composedPath = pnc.pathConditions.concat(c.pathConditions);
    let savedPathConditions = pnc.savedPathConditions;
    if (pnc.consequent instanceof AbruptCompletion) {
      if (pnc.alternate instanceof Value) {
        let [, g, b, p, o] = pnc.alternateEffects;
        let newAlternateEffects = [c, g, b, p, o];
        return new PossiblyNormalCompletion(
          c.value,
          pnc.joinCondition,
          pnc.consequent,
          pnc.consequentEffects,
          c,
          newAlternateEffects,
          composedPath,
          savedPathConditions,
          pnc.savedEffects
        );
      }
      invariant(pnc.alternate instanceof PossiblyNormalCompletion);
      let new_alternate = this.composePossiblyNormalCompletions(realm, pnc.alternate, c);
      let [, g, b, p, o] = pnc.alternateEffects;
      let newAlternateEffects = [new_alternate, g, b, p, o];
      return new PossiblyNormalCompletion(
        new_alternate.value,
        pnc.joinCondition,
        pnc.consequent,
        pnc.consequentEffects,
        new_alternate,
        newAlternateEffects,
        composedPath,
        savedPathConditions,
        pnc.savedEffects
      );
    } else {
      invariant(pnc.alternate instanceof AbruptCompletion);
      if (pnc.consequent instanceof Value) {
        let [, g, b, p, o] = pnc.consequentEffects;
        let newConsequentEffects = [c, g, b, p, o];
        return new PossiblyNormalCompletion(
          c.value,
          pnc.joinCondition,
          c,
          newConsequentEffects,
          pnc.alternate,
          pnc.alternateEffects,
          composedPath,
          savedPathConditions,
          pnc.savedEffects
        );
      }
      invariant(pnc.consequent instanceof PossiblyNormalCompletion);
      let new_consequent = this.composePossiblyNormalCompletions(realm, pnc.consequent, c);
      let [, g, b, p, o] = pnc.consequentEffects;
      let newConsequentEffects = [new_consequent, g, b, p, o];
      return new PossiblyNormalCompletion(
        new_consequent.value,
        pnc.joinCondition,
        new_consequent,
        newConsequentEffects,
        pnc.alternate,
        pnc.alternateEffects,
        composedPath,
        savedPathConditions,
        pnc.savedEffects
      );
    }
  }

  updatePossiblyNormalCompletionWithSubsequentEffects(
    realm: Realm,
    pnc: PossiblyNormalCompletion,
    subsequentEffects: Effects
  ) {
    let v = subsequentEffects[0];
    invariant(v instanceof Value);
    pnc.value = v;
    if (pnc.consequent instanceof AbruptCompletion) {
      if (pnc.alternate instanceof Value) {
        pnc.alternate = v;
        pnc.alternateEffects = realm.composeEffects(pnc.alternateEffects, subsequentEffects);
      } else {
        invariant(pnc.alternate instanceof PossiblyNormalCompletion);
        this.updatePossiblyNormalCompletionWithSubsequentEffects(realm, pnc.alternate, subsequentEffects);
      }
    } else {
      if (pnc.consequent instanceof Value) {
        pnc.consequent = v;
        pnc.consequentEffects = realm.composeEffects(pnc.consequentEffects, subsequentEffects);
      } else {
        invariant(pnc.consequent instanceof PossiblyNormalCompletion);
        this.updatePossiblyNormalCompletionWithSubsequentEffects(realm, pnc.consequent, subsequentEffects);
      }
    }
  }

  updatePossiblyNormalCompletionWithValue(realm: Realm, pnc: PossiblyNormalCompletion, v: Value) {
    pnc.value = v;
    if (pnc.consequent instanceof AbruptCompletion) {
      if (pnc.alternate instanceof Value) {
        pnc.alternate = v;
        pnc.alternateEffects[0] = v;
      } else {
        invariant(pnc.alternate instanceof PossiblyNormalCompletion);
        this.updatePossiblyNormalCompletionWithValue(realm, pnc.alternate, v);
      }
    } else {
      if (pnc.consequent instanceof Value) {
        pnc.consequent = v;
        pnc.consequentEffects[0] = v;
      } else {
        invariant(pnc.consequent instanceof PossiblyNormalCompletion);
        this.updatePossiblyNormalCompletionWithValue(realm, pnc.consequent, v);
      }
    }
  }

  // Returns the joined effects of all of the paths in pnc.
  // The normal path in pnc is modified to become terminated by ac,
  // so the overall completion will always be an instance of JoinedAbruptCompletions
  joinPossiblyNormalCompletionWithAbruptCompletion(
    realm: Realm,
    // a forked path with a non abrupt (normal) component
    pnc: PossiblyNormalCompletion,
    // an abrupt completion that completes the normal path
    ac: AbruptCompletion,
    // effects collected after pnc was constructed
    e: Effects
  ): Effects {
    // set up e with ac as the completion. It's OK to do this repeatedly since ac is not changed by recursive calls.
    e[0] = ac;
    if (pnc.consequent instanceof AbruptCompletion) {
      if (pnc.alternate instanceof Value) {
        return this.joinEffects(
          realm,
          pnc.joinCondition,
          pnc.consequentEffects,
          realm.composeEffects(pnc.alternateEffects, e)
        );
      }
      invariant(pnc.alternate instanceof PossiblyNormalCompletion);
      let alternate_effects = this.joinPossiblyNormalCompletionWithAbruptCompletion(realm, pnc.alternate, ac, e);
      invariant(pnc.consequent instanceof AbruptCompletion);
      return this.joinEffects(realm, pnc.joinCondition, pnc.consequentEffects, alternate_effects);
    } else {
      invariant(pnc.alternate instanceof AbruptCompletion);
      if (pnc.consequent instanceof Value) {
        return this.joinEffects(
          realm,
          pnc.joinCondition,
          realm.composeEffects(pnc.consequentEffects, e),
          pnc.alternateEffects
        );
      }
      invariant(pnc.consequent instanceof PossiblyNormalCompletion);
      let consequent_effects = this.joinPossiblyNormalCompletionWithAbruptCompletion(realm, pnc.consequent, ac, e);
      invariant(pnc.alternate instanceof AbruptCompletion);
      return this.joinEffects(realm, pnc.joinCondition, consequent_effects, pnc.alternateEffects);
    }
  }

  joinPossiblyNormalCompletionWithValue(
    realm: Realm,
    joinCondition: AbstractValue,
    pnc: PossiblyNormalCompletion,
    v: Value
  ) {
    if (pnc.consequent instanceof AbruptCompletion) {
      if (pnc.alternate instanceof Value) {
        pnc.alternate = this.joinValuesAsConditional(realm, joinCondition, pnc.alternate, v);
      } else {
        invariant(pnc.alternate instanceof PossiblyNormalCompletion);
        this.joinPossiblyNormalCompletionWithValue(realm, joinCondition, pnc.alternate, v);
      }
    } else {
      if (pnc.consequent instanceof Value) {
        pnc.consequent = this.joinValuesAsConditional(realm, joinCondition, pnc.consequent, v);
      } else {
        invariant(pnc.consequent instanceof PossiblyNormalCompletion);
        this.joinPossiblyNormalCompletionWithValue(realm, joinCondition, pnc.consequent, v);
      }
    }
  }

  joinValueWithPossiblyNormalCompletion(
    realm: Realm,
    joinCondition: AbstractValue,
    pnc: PossiblyNormalCompletion,
    v: Value
  ) {
    if (pnc.consequent instanceof AbruptCompletion) {
      if (pnc.alternate instanceof Value) {
        pnc.alternate = this.joinValuesAsConditional(realm, joinCondition, v, pnc.alternate);
      } else {
        invariant(pnc.alternate instanceof PossiblyNormalCompletion);
        this.joinValueWithPossiblyNormalCompletion(realm, joinCondition, pnc.alternate, v);
      }
    } else {
      if (pnc.consequent instanceof Value) {
        pnc.consequent = this.joinValuesAsConditional(realm, joinCondition, v, pnc.consequent);
      } else {
        invariant(pnc.consequent instanceof PossiblyNormalCompletion);
        this.joinValueWithPossiblyNormalCompletion(realm, joinCondition, pnc.consequent, v);
      }
    }
  }

  joinPossiblyNormalCompletions(
    realm: Realm,
    joinCondition: AbstractValue,
    c: PossiblyNormalCompletion,
    a: PossiblyNormalCompletion
  ): PossiblyNormalCompletion {
    let rJoinCondition: Value;
    let cp: [Effects, Effects];
    let ap: [Effects, Effects];
    if (c.consequent instanceof AbruptCompletion) {
      if (a.consequent instanceof AbruptCompletion) {
        rJoinCondition = AbstractValue.createFromLogicalOp(realm, "&&", c.joinCondition, a.joinCondition);
        cp = [c.consequentEffects, a.consequentEffects];
        ap = [c.alternateEffects, a.alternateEffects];
      } else {
        let notA = AbstractValue.createFromUnaryOp(realm, "!", a.joinCondition);
        rJoinCondition = AbstractValue.createFromLogicalOp(realm, "&&", c.joinCondition, notA);
        cp = [c.consequentEffects, a.alternateEffects];
        ap = [c.alternateEffects, a.consequentEffects];
      }
    } else {
      let notC = AbstractValue.createFromUnaryOp(realm, "!", c.joinCondition);
      if (a.consequent instanceof AbruptCompletion) {
        rJoinCondition = AbstractValue.createFromLogicalOp(realm, "&&", notC, a.joinCondition);
        cp = [c.alternateEffects, a.consequentEffects];
        ap = [c.consequentEffects, a.alternateEffects];
      } else {
        let notA = AbstractValue.createFromUnaryOp(realm, "!", a.joinCondition);
        rJoinCondition = AbstractValue.createFromLogicalOp(realm, "&&", notC, notA);
        cp = [c.alternateEffects, a.alternateEffects];
        ap = [c.consequentEffects, a.consequentEffects];
      }
    }
    invariant(rJoinCondition instanceof AbstractValue); // the transformations will not result in tautologies
    let [ce1, ce2] = cp;
    let [ae1, ae2] = ap;
    let rce = this.joinEffects(realm, joinCondition, ce1, ce2);
    let rae = this.joinEffects(realm, joinCondition, ae1, ae2);
    let rc = rce[0];
    invariant(rc instanceof Value || rc instanceof Completion);
    let ra = rae[0];
    invariant(ra instanceof Value || ra instanceof Completion);
    let rv = ra instanceof PossiblyNormalCompletion ? ra.value : ra;
    invariant(rv instanceof Value);
    return new PossiblyNormalCompletion(rv, rJoinCondition, rc, rce, ra, rae, [], []);
  }

  joinAndRemoveNestedReturnCompletions(
    realm: Realm,
    c: AbruptCompletion
  ): AbruptCompletion | PossiblyNormalCompletion | Value {
    if (c instanceof ReturnCompletion) {
      return c.value;
    }
    if (c instanceof JoinedAbruptCompletions) {
      let c1 = this.joinAndRemoveNestedReturnCompletions(realm, c.consequent);
      let c2 = this.joinAndRemoveNestedReturnCompletions(realm, c.alternate);
      c.consequentEffects[0] = c1;
      c.alternateEffects[0] = c2;
      return this.joinResults(realm, c.joinCondition, c1, c2, c.consequentEffects, c.alternateEffects);
    }
    return c;
  }

  joinEffectsAndPromoteNestedReturnCompletions(
    realm: Realm,
    c: Completion | Value,
    e: Effects,
    nested_effects?: Effects
  ): Effects {
    if (c instanceof Value) {
      // If not undefined, the nested effects were captured when evaluating a conditional code block that ended normally.
      // e represent effects that were captured since reaching the join point where the normal and abrupt
      // completions came together into the completion supplied to the outermost call to this recursive function.
      if (nested_effects !== undefined) e = realm.composeEffects(nested_effects, e);
      return e;
    }
    if (c instanceof AbruptCompletion && !(c instanceof JoinedAbruptCompletions)) {
      // The nested effects were captured when evaluating a conditional code block that ended abruptly.
      // An abrupt completion does not care about the effects that were collected since the join point.
      invariant(nested_effects !== undefined);
      return nested_effects;
    }
    if (c instanceof PossiblyNormalCompletion) {
      let e1 = this.joinEffectsAndPromoteNestedReturnCompletions(realm, c.consequent, e, c.consequentEffects);
      let e2 = this.joinEffectsAndPromoteNestedReturnCompletions(realm, c.alternate, e, c.alternateEffects);
      if (e1[0] instanceof AbruptCompletion) {
        if (e2[0] instanceof Value) e2[0] = new ReturnCompletion(realm.intrinsics.undefined, realm.currentLocation);
        return this.joinEffects(realm, c.joinCondition, e1, e2);
      } else if (e2[0] instanceof AbruptCompletion) {
        if (e1[0] instanceof Value) e1[0] = new ReturnCompletion(realm.intrinsics.undefined, realm.currentLocation);
        return this.joinEffects(realm, c.joinCondition, e1, e2);
      }
    }
    invariant(c instanceof JoinedAbruptCompletions);
    // e will be ignored in the calls below since the branches are all abrupt.
    let e1 = this.joinEffectsAndPromoteNestedReturnCompletions(realm, c.consequent, e, c.consequentEffects);
    let e2 = this.joinEffectsAndPromoteNestedReturnCompletions(realm, c.alternate, e, c.alternateEffects);
    let [r1, r2] = [e1[0], e2[0]];
    if (r1 instanceof ReturnCompletion) {
      invariant(!(r2 instanceof ReturnCompletion)); // Otherwise their values should have been joined
      if (r2 instanceof JoinedAbruptCompletions) {
        if (r2.consequent instanceof ReturnCompletion) {
          let r1jr2c = this.joinEffects(realm, c.joinCondition, e1, r2.consequentEffects);
          invariant(r1jr2c[0] instanceof ReturnCompletion);
          let or = AbstractValue.createFromLogicalOp(realm, "||", c.joinCondition, r2.joinCondition);
          invariant(or instanceof AbstractValue);
          return this.joinEffects(realm, or, r1jr2c, r2.alternateEffects);
        }
        if (r2.alternate instanceof ReturnCompletion) {
          let r1jr2a = this.joinEffects(realm, c.joinCondition, e1, r2.alternateEffects);
          invariant(r1jr2a[0] instanceof ReturnCompletion);
          let notR2jc = AbstractValue.createFromUnaryOp(realm, "!", r2.joinCondition);
          let or = AbstractValue.createFromLogicalOp(realm, "||", c.joinCondition, notR2jc);
          invariant(or instanceof AbstractValue);
          return this.joinEffects(realm, or, r1jr2a, r2.consequentEffects);
        }
      }
    } else if (r2 instanceof ReturnCompletion) {
      invariant(!(r1 instanceof ReturnCompletion)); // Otherwise their values should have been joined
      if (r1 instanceof JoinedAbruptCompletions) {
        if (r1.consequent instanceof ReturnCompletion) {
          let r2jr1c = this.joinEffects(realm, c.joinCondition, r1.consequentEffects, e2);
          invariant(r2jr1c[0] instanceof ReturnCompletion);
          let or = AbstractValue.createFromLogicalOp(realm, "||", c.joinCondition, r1.joinCondition);
          invariant(or instanceof AbstractValue);
          return this.joinEffects(realm, or, r2jr1c, r1.alternateEffects);
        }
        if (r1.alternate instanceof ReturnCompletion) {
          let r2jr1a = this.joinEffects(realm, c.joinCondition, r1.alternateEffects, e2);
          let notR1jc = AbstractValue.createFromUnaryOp(realm, "!", r1.joinCondition);
          invariant(r2jr1a[0] instanceof ReturnCompletion);
          let or = AbstractValue.createFromLogicalOp(realm, "||", c.joinCondition, notR1jc);
          invariant(or instanceof AbstractValue);
          return this.joinEffects(realm, or, r2jr1a, r1.consequentEffects);
        }
      }
    }
    return this.joinEffects(realm, c.joinCondition, e1, e2);
  }

  unbundleReturnCompletion(realm: Realm, c: JoinedAbruptCompletions): [Effects, PossiblyNormalCompletion] {
    let empty_effects = construct_empty_effects(realm);
    let v = realm.intrinsics.empty;
    if (c.consequent instanceof ReturnCompletion) {
      let negation = AbstractValue.createFromUnaryOp(realm, "!", c.joinCondition);
      // Simply negating the (known to be abstract) join condition should
      // not become a concrete value
      invariant(negation instanceof AbstractValue);
      let pathConditions = [negation];
      let pnc = new PossiblyNormalCompletion(
        v,
        c.joinCondition,
        v,
        empty_effects,
        c.alternate,
        c.alternateEffects,
        pathConditions,
        []
      );
      return [c.consequentEffects, pnc];
    } else if (c.alternate instanceof ReturnCompletion) {
      let pnc = new PossiblyNormalCompletion(
        v,
        c.joinCondition,
        c.consequent,
        c.consequentEffects,
        v,
        empty_effects,
        [c.joinCondition],
        []
      );
      return [c.alternateEffects, pnc];
    } else {
      invariant(false, "unbundleReturnCompletion needs an argument that contains a non nested return completion");
    }
  }

  removeNormalEffects(realm: Realm, c: PossiblyNormalCompletion): Effects {
    if (c.consequent instanceof AbruptCompletion) {
      if (c.alternate instanceof Value) {
        let result = c.alternateEffects;
        c.alternateEffects = construct_empty_effects(realm);
        return result;
      } else {
        invariant(c.alternate instanceof PossiblyNormalCompletion);
        let result = realm.composeEffects(c.alternateEffects, this.removeNormalEffects(realm, c.alternate));
        c.alternateEffects = construct_empty_effects(realm);
        return result;
      }
    } else {
      if (c.consequent instanceof Value) {
        let result = c.consequentEffects;
        c.consequentEffects = construct_empty_effects(realm);
        return result;
      } else {
        invariant(c.consequent instanceof PossiblyNormalCompletion);
        let result = realm.composeEffects(c.consequentEffects, this.removeNormalEffects(realm, c.consequent));
        c.consequentEffects = construct_empty_effects(realm);
        return result;
      }
    }
  }

  joinEffects(realm: Realm, joinCondition: AbstractValue, e1: Effects, e2: Effects): Effects {
    let [result1, gen1, bindings1, properties1, createdObj1] = e1;
    let [result2, gen2, bindings2, properties2, createdObj2] = e2;

    let result = this.joinResults(realm, joinCondition, result1, result2, e1, e2);
    if (result1 instanceof AbruptCompletion) {
      if (!(result2 instanceof AbruptCompletion)) {
        invariant(result instanceof PossiblyNormalCompletion);
        return [result, gen2, bindings2, properties2, createdObj2];
      }
    } else if (result2 instanceof AbruptCompletion) {
      invariant(result instanceof PossiblyNormalCompletion);
      return [result, gen1, bindings1, properties1, createdObj1];
    }

    let bindings = this.joinBindings(realm, joinCondition, bindings1, bindings2);
    let properties = this.joinPropertyBindings(
      realm,
      joinCondition,
      properties1,
      properties2,
      createdObj1,
      createdObj2
    );
    let createdObjects = new Set();
    createdObj1.forEach(o => {
      createdObjects.add(o);
    });
    createdObj2.forEach(o => {
      createdObjects.add(o);
    });

    let generator = joinGenerators(realm, joinCondition, gen1, gen2);

    return [result, generator, bindings, properties, createdObjects];
  }

  joinResults(
    realm: Realm,
    joinCondition: AbstractValue,
    result1: EvaluationResult,
    result2: EvaluationResult,
    e1: Effects,
    e2: Effects
  ): AbruptCompletion | PossiblyNormalCompletion | Value {
    let getAbstractValue = (v1: void | Value, v2: void | Value) => {
      return this.joinValuesAsConditional(realm, joinCondition, v1, v2);
    };
    if (result1 instanceof Reference || result2 instanceof Reference) {
      AbstractValue.reportIntrospectionError(joinCondition);
      throw new FatalError();
    }
    if (result1 instanceof BreakCompletion && result2 instanceof BreakCompletion && result1.target === result2.target) {
      return new BreakCompletion(realm.intrinsics.empty, joinCondition.expressionLocation, result1.target);
    }
    if (
      result1 instanceof ContinueCompletion &&
      result2 instanceof ContinueCompletion &&
      result1.target === result2.target
    ) {
      return new ContinueCompletion(realm.intrinsics.empty, joinCondition.expressionLocation, result1.target);
    }
    if (result1 instanceof ReturnCompletion && result2 instanceof ReturnCompletion) {
      let val = this.joinValues(realm, result1.value, result2.value, getAbstractValue);
      invariant(val instanceof Value);
      return new ReturnCompletion(val, joinCondition.expressionLocation);
    }
    if (result1 instanceof ThrowCompletion && result2 instanceof ThrowCompletion) {
      let val = this.joinValues(realm, result1.value, result2.value, getAbstractValue);
      invariant(val instanceof Value);
      return new ThrowCompletion(val, result1.location);
    }
    if (result1 instanceof AbruptCompletion && result2 instanceof AbruptCompletion) {
      return new JoinedAbruptCompletions(realm, joinCondition, result1, e1, result2, e2);
    }
    if (result1 instanceof Value && result2 instanceof Value) {
      let val = this.joinValues(realm, result1, result2, getAbstractValue);
      invariant(val instanceof Value);
      return val;
    }
    if (result1 instanceof PossiblyNormalCompletion && result2 instanceof PossiblyNormalCompletion) {
      return this.joinPossiblyNormalCompletions(realm, joinCondition, result1, result2);
    }
    if (result1 instanceof AbruptCompletion) {
      let value = result2;
      let savedEffects;
      let pathConditions;
      let savedPathConditions = [];
      if (result2 instanceof PossiblyNormalCompletion) {
        value = result2.value;
        savedEffects = result2.savedEffects;
        pathConditions = [joinCondition].concat(result2.pathConditions);
        savedPathConditions = result2.savedPathConditions;
      } else {
        pathConditions = [joinCondition];
      }
      invariant(value instanceof Value);
      return new PossiblyNormalCompletion(
        value,
        joinCondition,
        result1,
        e1,
        result2,
        e2,
        pathConditions,
        savedPathConditions,
        savedEffects
      );
    }
    if (result2 instanceof AbruptCompletion) {
      let value = result1;
      let savedEffects;
      let pathConditions;
      let savedPathConditions = [];
      if (result1 instanceof PossiblyNormalCompletion) {
        value = result1.value;
        savedEffects = result1.savedEffects;
        pathConditions = [joinCondition].concat(result1.pathConditions);
        savedPathConditions = result1.savedPathConditions;
      } else {
        pathConditions = [joinCondition];
      }
      invariant(value instanceof Value);
      return new PossiblyNormalCompletion(
        value,
        joinCondition,
        result1,
        e1,
        result2,
        e2,
        pathConditions,
        savedPathConditions,
        savedEffects
      );
    }
    if (result1 instanceof PossiblyNormalCompletion) {
      invariant(result2 instanceof Value);
      this.joinPossiblyNormalCompletionWithValue(realm, joinCondition, result1, result2);
      return result1;
    }
    if (result2 instanceof PossiblyNormalCompletion) {
      invariant(result1 instanceof Value);
      this.joinValueWithPossiblyNormalCompletion(realm, joinCondition, result2, result1);
      return result2;
    }
    invariant(false);
  }

  composeGenerators(realm: Realm, generator1: Generator, generator2: Generator): Generator {
    let result = new Generator(realm);
    if (!generator1.empty() || !generator2.empty()) {
      result.composeGenerators(generator1, generator2);
    }
    return result;
  }

  // Creates a single map that joins together maps m1 and m2 using the given join
  // operator. If an entry is present in one map but not the other, the missing
  // entry is treated as if it were there and its value were undefined.
  joinMaps<K, V>(m1: Map<K, V>, m2: Map<K, V>, join: (K, void | V, void | V) => V): Map<K, V> {
    let m3: Map<K, V> = new Map();
    m1.forEach((val1, key, map1) => {
      let val2 = m2.get(key);
      let val3 = join(key, val1, val2);
      m3.set(key, val3);
    });
    m2.forEach((val2, key, map2) => {
      if (!m1.has(key)) {
        m3.set(key, join(key, undefined, val2));
      }
    });
    return m3;
  }

  // Creates a single map that has an key, value pair for the union of the key
  // sets of m1 and m2. The value of a pair is the join of m1[key] and m2[key]
  // where the join is defined to be just m1[key] if m1[key] === m2[key] and
  // and abstract value with expression "joinCondition ? m1[key] : m2[key]" if not.
  joinBindings(realm: Realm, joinCondition: AbstractValue, m1: Bindings, m2: Bindings): Bindings {
    let getAbstractValue = (v1: void | Value, v2: void | Value) => {
      return this.joinValuesAsConditional(realm, joinCondition, v1, v2);
    };
    let join = (b: Binding, b1: void | BindingEntry, b2: void | BindingEntry) => {
      let l1 = b1 === undefined ? b.hasLeaked : b1.hasLeaked;
      let l2 = b2 === undefined ? b.hasLeaked : b2.hasLeaked;
      let v1 = b1 === undefined ? b.value : b1.value;
      let v2 = b2 === undefined ? b.value : b2.value;
      let hasLeaked = l1 || l2; // If either has leaked, then this binding has leaked.
      let value = this.joinValues(realm, v1, v2, getAbstractValue);
      invariant(value instanceof Value);
      return { hasLeaked, value };
    };
    return this.joinMaps(m1, m2, join);
  }

  // If v1 is known and defined and v1 === v2 return v1,
  // otherwise return getAbstractValue(v1, v2)
  joinValues(
    realm: Realm,
    v1: void | Value | Array<Value> | Array<{ $Key: void | Value, $Value: void | Value }>,
    v2: void | Value | Array<Value> | Array<{ $Key: void | Value, $Value: void | Value }>,
    getAbstractValue: (void | Value, void | Value) => Value
  ): Value | Array<Value> | Array<{ $Key: void | Value, $Value: void | Value }> {
    if (Array.isArray(v1) || Array.isArray(v2)) {
      invariant(v1 === undefined || Array.isArray(v1));
      invariant(v2 === undefined || Array.isArray(v2));
      return joinArrays(realm, ((v1: any): void | Array<Value>), ((v2: any): void | Array<Value>), getAbstractValue);
    }
    invariant(v1 === undefined || v1 instanceof Value);
    invariant(v2 === undefined || v2 instanceof Value);
    if (
      v1 !== undefined &&
      v2 !== undefined &&
      !(v1 instanceof AbstractValue) &&
      !(v2 instanceof AbstractValue) &&
      StrictEqualityComparison(realm, v1.throwIfNotConcrete(), v2.throwIfNotConcrete())
    ) {
      return v1;
    } else {
      return getAbstractValue(v1, v2);
    }
  }

  joinValuesAsConditional(realm: Realm, condition: AbstractValue, v1: void | Value, v2: void | Value): Value {
    return AbstractValue.createFromConditionalOp(realm, condition, v1, v2);
  }

  joinPropertyBindings(
    realm: Realm,
    joinCondition: AbstractValue,
    m1: PropertyBindings,
    m2: PropertyBindings,
    c1: CreatedObjects,
    c2: CreatedObjects
  ): PropertyBindings {
    let join = (b: PropertyBinding, d1: void | Descriptor, d2: void | Descriptor) => {
      // If the PropertyBinding object has been freshly allocated do not join
      if (d1 === undefined) {
        if (b.object instanceof ObjectValue && c2.has(b.object)) return d2; // no join
        if (b.descriptor !== undefined && m1.has(b)) {
          // property was deleted
          d1 = cloneDescriptor(b.descriptor);
          invariant(d1 !== undefined);
          d1.value = realm.intrinsics.empty;
        } else {
          // no write to property
          d1 = b.descriptor; //Get value of property before the split
        }
      }
      if (d2 === undefined) {
        if (b.object instanceof ObjectValue && c1.has(b.object)) return d1; // no join
        if (b.descriptor !== undefined && m2.has(b)) {
          // property was deleted
          d2 = cloneDescriptor(b.descriptor);
          invariant(d2 !== undefined);
          d2.value = realm.intrinsics.empty;
        } else {
          // no write to property
          d2 = b.descriptor; //Get value of property before the split
        }
      }
      return this.joinDescriptors(realm, joinCondition, d1, d2);
    };
    return this.joinMaps(m1, m2, join);
  }

  joinDescriptors(
    realm: Realm,
    joinCondition: AbstractValue,
    d1: void | Descriptor,
    d2: void | Descriptor
  ): void | Descriptor {
    let getAbstractValue = (v1: void | Value, v2: void | Value) => {
      return this.joinValuesAsConditional(realm, joinCondition, v1, v2);
    };
    let clone_with_abstract_value = (d: Descriptor) => {
      if (!IsDataDescriptor(realm, d)) {
        let d3: Descriptor = {};
        d3.joinCondition = joinCondition;
        return d3;
      }
      let dc = cloneDescriptor(d);
      invariant(dc !== undefined);
      let dcValue = dc.value;
      if (Array.isArray(dcValue)) {
        invariant(dcValue.length > 0);
        let elem0 = dcValue[0];
        if (elem0 instanceof Value) {
          dc.value = dcValue.map(e => getAbstractValue((e: any), realm.intrinsics.empty));
        } else {
          dc.value = dcValue.map(e => {
            let { $Key: key1, $Value: val1 } = (e: any);
            let key3 = getAbstractValue(key1, realm.intrinsics.empty);
            let val3 = getAbstractValue(val1, realm.intrinsics.empty);
            return { $Key: key3, $Value: val3 };
          });
        }
      } else {
        invariant(dcValue === undefined || dcValue instanceof Value);
        dc.value = getAbstractValue(dcValue, realm.intrinsics.empty);
      }
      return dc;
    };
    if (d1 === undefined) {
      if (d2 === undefined) return undefined;
      // d2 is a new property created in only one branch, join with empty
      let d3 = clone_with_abstract_value(d2);
      if (!IsDataDescriptor(realm, d2)) d3.descriptor2 = d2;
      return d3;
    } else if (d2 === undefined) {
      invariant(d1 !== undefined);
      // d1 is a new property created in only one branch, join with empty
      let d3 = clone_with_abstract_value(d1);
      if (!IsDataDescriptor(realm, d1)) d3.descriptor1 = d1;
      return d3;
    } else {
      if (equalDescriptors(d1, d2) && IsDataDescriptor(realm, d1)) {
        let dc = cloneDescriptor(d1);
        invariant(dc !== undefined);
        dc.value = this.joinValues(realm, d1.value, d2.value, getAbstractValue);
        return dc;
      }
      let d3: Descriptor = {};
      d3.joinCondition = joinCondition;
      d3.descriptor1 = d1;
      d3.descriptor2 = d2;
      return d3;
    }
  }
}
