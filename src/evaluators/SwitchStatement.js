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
import type { LexicalEnvironment } from "../environment.js";
import { CompilerDiagnostic } from "../errors.js";
import { Reference } from "../environment.js";
import { computeBinary } from "./BinaryExpression.js";
import { AbruptCompletion, BreakCompletion, PossiblyNormalCompletion, Completion } from "../completions.js";
import { InternalGetResultValue } from "./ForOfStatement.js";
import { EmptyValue, AbstractValue, Value } from "../values/index.js";
import { StrictEqualityComparisonPartial, UpdateEmpty } from "../methods/index.js";
import { Environment, Path, Join } from "../singletons.js";
import { FatalError } from "../errors.js";
import type { BabelNodeSwitchStatement, BabelNodeSwitchCase, BabelNodeExpression } from "babel-types";
import invariant from "../invariant.js";

// 13.12.10 Runtime Semantics: CaseSelectorEvaluation
function CaseSelectorEvaluation(
  expression: BabelNodeExpression,
  strictCode: boolean,
  env: LexicalEnvironment,
  realm: Realm
): Value {
  // 1. Let exprRef be the result of evaluating Expression.
  let exprRef = env.evaluate(expression, strictCode);

  // 2. Return ? GetValue(exprRef).
  return Environment.GetValue(realm, exprRef);
}

function AbstractCaseBlockEvaluation(
  cases: Array<BabelNodeSwitchCase>,
  defaultCaseIndex: number,
  input: Value,
  strictCode: boolean,
  env: LexicalEnvironment,
  realm: Realm
): Value {
  invariant(realm.useAbstractInterpretation);

  let DefiniteCaseEvaluation = (caseIndex: number): Value => {
    let result = realm.intrinsics.undefined;
    // we start at the case we've been asked to evaluate, and process statements
    // until there is either a break statement or exception thrown (this means we
    // implicitly fall through correctly in the absence of a break statement).
    while (caseIndex < cases.length) {
      let c = cases[caseIndex];
      for (let i = 0; i < c.consequent.length; i += 1) {
        let node = c.consequent[i];
        let r = env.evaluateCompletion(node, strictCode);
        invariant(!(r instanceof Reference));

        if (r instanceof PossiblyNormalCompletion) {
          // TODO correct handling of PossiblyNormal and AbruptCompletion
          let diagnostic = new CompilerDiagnostic(
            "case block containing a throw, return or continue is not yet supported",
            r.location,
            "PP0027",
            "FatalError"
          );
          realm.handleError(diagnostic);
          throw new FatalError();
        }

        result = UpdateEmpty(realm, r, result);
        if (result instanceof Completion) break;
      }

      if (result instanceof Completion) break;
      caseIndex++;
    }

    if (result instanceof BreakCompletion) {
      return result.value;
    } else if (result instanceof AbruptCompletion) {
      // TODO correct handling of PossiblyNormal and AbruptCompletion
      let diagnostic = new CompilerDiagnostic(
        "case block containing a throw, return or continue is not yet supported",
        result.location,
        "PP0027",
        "FatalError"
      );
      realm.handleError(diagnostic);
      throw new FatalError();
    } else {
      invariant(result instanceof Value);
      return result;
    }
  };

  let AbstractCaseEvaluation = (caseIndex: number): Value => {
    if (caseIndex === defaultCaseIndex) {
      // skip the default case until we've exhausted all other options
      return AbstractCaseEvaluation(caseIndex + 1);
    } else if (caseIndex >= cases.length) {
      // this is the stop condition for our recursive search for a matching case.
      // we tried every available case index and since nothing matches we return
      // the default (and if none exists....just empty)
      if (defaultCaseIndex !== -1) {
        return DefiniteCaseEvaluation(defaultCaseIndex);
      } else {
        return realm.intrinsics.empty;
      }
    }
    // else we have a normal in-range case index

    let c = cases[caseIndex];
    let test = c.test;
    invariant(test);

    let selector = CaseSelectorEvaluation(test, strictCode, env, realm);
    let selectionResult = computeBinary(realm, "===", input, selector);

    if (!selectionResult.mightNotBeTrue()) {
      //  we have a winning result for the switch case, bubble it back up!
      return DefiniteCaseEvaluation(caseIndex);
    } else if (!selectionResult.mightNotBeFalse()) {
      // we have a case that is definitely *not* taken
      // so we go and look at the next one in the hope of finding a match
      return AbstractCaseEvaluation(caseIndex + 1);
    } else {
      invariant(selectionResult instanceof AbstractValue);
      // we can't be sure whether the case selector evaluates true or not
      // so we evaluate the case in the abstract as an if-else with the else
      // leading to the next case statement
      let trueEffects = Path.withCondition(selectionResult, () => {
        return realm.evaluateForEffects(
          () => {
            return DefiniteCaseEvaluation(caseIndex);
          },
          undefined,
          "AbstractCaseEvaluation/1"
        );
      });

      let falseEffects = Path.withInverseCondition(selectionResult, () => {
        return realm.evaluateForEffects(
          () => {
            return AbstractCaseEvaluation(caseIndex + 1);
          },
          undefined,
          "AbstractCaseEvaluation/2"
        );
      });

      let joinedEffects = Join.joinEffects(realm, selectionResult, trueEffects, falseEffects);
      let completion = joinedEffects[0];
      if (completion instanceof PossiblyNormalCompletion) {
        // in this case one of the branches may complete abruptly, which means that
        // not all control flow branches join into one flow at this point.
        // Consequently we have to continue tracking changes until the point where
        // all the branches come together into one.
        completion = realm.composeWithSavedCompletion(completion);
      }
      // Note that the effects of (non joining) abrupt branches are not included
      // in joinedEffects, but are tracked separately inside completion.
      realm.applyEffects(joinedEffects);

      // return or throw completion
      if (completion instanceof AbruptCompletion) throw completion;
      invariant(completion instanceof Value);
      return completion;
    }
  };

  // let the recursive search for a matching case begin!
  return AbstractCaseEvaluation(0);
}

function CaseBlockEvaluation(
  cases: Array<BabelNodeSwitchCase>,
  input: Value,
  strictCode: boolean,
  env: LexicalEnvironment,
  realm: Realm
): Value {
  let EvaluateCase = (c: BabelNodeSwitchCase): Value | AbruptCompletion => {
    let r = realm.intrinsics.empty;
    for (let node of c.consequent) {
      let res = env.evaluateCompletion(node, strictCode);
      if (res instanceof AbruptCompletion) return (UpdateEmpty(realm, res, r): any);
      if (!(res instanceof EmptyValue)) r = res;
    }
    return r;
  };

  let EvaluateCaseClauses = (A: Array<BabelNodeSwitchCase>, V: Value): [boolean, Value] => {
    // 2. Let A be the List of CaseClause items in CaseClauses, in source text order.
    // A is passed in

    // 3. Let found be false.
    let found = false;

    // 4. Repeat for each CaseClause C in A,
    for (let C of A) {
      // a. If found is false, then
      if (!found) {
        // i. Let clauseSelector be the result of CaseSelectorEvaluation of C.
        let test = C.test;
        invariant(test);
        let clauseSelector = CaseSelectorEvaluation(test, strictCode, env, realm);

        // ii. ReturnIfAbrupt(clauseSelector).
        // above will throw a Completion which will return

        // iii. Let found be the result of performing Strict Equality Comparison input === clauseSelector.[[Value]].
        found = StrictEqualityComparisonPartial(realm, input, clauseSelector);
      }
      if (found) {
        // b. If found is true, then
        // i. Let R be the result of evaluating C.
        let R = EvaluateCase(C);

        // ii. If R.[[Value]] is not empty, let V be R.[[Value]].
        let val = InternalGetResultValue(realm, R);
        if (!(val instanceof EmptyValue)) V = val;

        // iii. If R is an abrupt completion, return Completion(UpdateEmpty(R, V)).
        if (R instanceof AbruptCompletion) {
          throw UpdateEmpty(realm, R, V);
        }
      }
    }
    return [found, V];
  };

  // CaseBlock:{}
  // 1. Return NormalCompletion(undefined).
  if (cases.length === 0) return realm.intrinsics.undefined;

  // CaseBlock:{CaseClauses DefaultClause CaseClauses}
  let default_case_num = cases.findIndex(clause => {
    return clause.test === null;
  });

  // Abstract interpretation of case blocks is a significantly different process
  // from regular interpretation, so we fork off early to keep things tidily separated.
  if (input instanceof AbstractValue) {
    return AbstractCaseBlockEvaluation(cases, default_case_num, input, strictCode, env, realm);
  }

  if (default_case_num !== -1) {
    // 2. Let A be the List of CaseClause items in the first CaseClauses, in source text order. If the first CaseClauses is not present, A is « ».
    let A = cases.slice(0, default_case_num);

    let V = realm.intrinsics.undefined;

    // 4. Repeat for each CaseClause C in A
    [, V] = EvaluateCaseClauses(A, V);

    // 5. Let foundInB be false.
    let foundInB = false;

    // 6. Let B be the List containing the CaseClause items in the second CaseClauses, in source text order. If the second CaseClauses is not present, B is « ».
    let B = cases.slice(default_case_num + 1);

    [foundInB, V] = EvaluateCaseClauses(B, V);

    // 8. If foundInB is true, return NormalCompletion(V).
    if (foundInB) return V;

    // 9. Let R be the result of evaluating DefaultClause.
    let R = EvaluateCase(cases[default_case_num]);

    // 10. If R.[[Value]] is not empty, let V be R.[[Value]].
    let val = InternalGetResultValue(realm, R);
    if (!(val instanceof EmptyValue)) V = val;

    // 11. If R is an abrupt completion, return Completion(UpdateEmpty(R, V)).
    if (R instanceof AbruptCompletion) {
      throw UpdateEmpty(realm, R, V);
    }

    // 12: Repeat for each CaseClause C in B (NOTE this is another complete iteration of the second CaseClauses)
    for (let C of B) {
      // a. Let R be the result of evaluating CaseClause C.
      R = EvaluateCase(C);

      // b. If R.[[Value]] is not empty, let V be R.[[Value]].
      let value = InternalGetResultValue(realm, R);
      if (!(value instanceof EmptyValue)) V = value;

      // c. If R is an abrupt completion, return Completion(UpdateEmpty(R, V)).
      if (R instanceof AbruptCompletion) {
        throw UpdateEmpty(realm, R, V);
      }
    }

    // 13. Return NormalCompletion(V).
    return V;
  } else {
    // CaseBlock:{CaseClauses}
    let V;
    [, V] = EvaluateCaseClauses(cases, realm.intrinsics.undefined);
    return V;
  }
}

// 13.12.11
export default function(
  ast: BabelNodeSwitchStatement,
  strictCode: boolean,
  env: LexicalEnvironment,
  realm: Realm,
  labelSet: Array<string>
): Value {
  let expression = ast.discriminant;
  let cases: Array<BabelNodeSwitchCase> = ast.cases;

  // 1. Let exprRef be the result of evaluating Expression.
  let exprRef = env.evaluate(expression, strictCode);

  // 2. Let switchValue be ? GetValue(exprRef).
  let switchValue = Environment.GetValue(realm, exprRef);

  // 3. Let oldEnv be the running execution context's LexicalEnvironment.
  let oldEnv = realm.getRunningContext().lexicalEnvironment;

  // 4. Let blockEnv be NewDeclarativeEnvironment(oldEnv).
  let blockEnv = Environment.NewDeclarativeEnvironment(realm, oldEnv);

  // 5. Perform BlockDeclarationInstantiation(CaseBlock, blockEnv).
  let CaseBlock = cases.map(c => c.consequent).reduce((stmts, case_blk) => stmts.concat(case_blk), []);
  Environment.BlockDeclarationInstantiation(realm, strictCode, CaseBlock, blockEnv);

  // 6. Set the running execution context's LexicalEnvironment to blockEnv.
  realm.getRunningContext().lexicalEnvironment = blockEnv;

  let R;
  try {
    // 7. Let R be the result of performing CaseBlockEvaluation of CaseBlock with argument switchValue.
    R = CaseBlockEvaluation(cases, switchValue, strictCode, blockEnv, realm);

    // 9. Return R.
    return R;
  } catch (e) {
    if (e instanceof BreakCompletion) {
      if (!e.target) return (UpdateEmpty(realm, e, realm.intrinsics.undefined): any).value;
    }
    throw e;
  } finally {
    // 8. Set the running execution context's LexicalEnvironment to oldEnv.
    realm.getRunningContext().lexicalEnvironment = oldEnv;
    realm.onDestroyScope(blockEnv);
  }
}
