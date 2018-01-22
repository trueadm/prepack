/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { BabelNodeCallExpression, BabelNodeSourceLocation } from "babel-types";
import { Completion, ThrowCompletion } from "../completions.js";
import { CompilerDiagnostic, FatalError } from "../errors.js";
import invariant from "../invariant.js";
import { type Effects, type PropertyBindings, Realm } from "../realm.js";
import type { AdditionalFunctionEffects, ReactBytecodeTree } from "./types.js";
import type { PropertyBinding } from "../types.js";
import { ignoreErrorsIn } from "../utils/errors.js";
import {
  Value,
  AbstractObjectValue,
  FunctionValue,
  ObjectValue,
  AbstractValue,
  ECMAScriptSourceFunctionValue,
} from "../values/index.js";
import { Get } from "../methods/index.js";
import { ModuleTracer } from "../utils/modules.js";
import buildTemplate from "babel-template";
import { ReactStatistics, type ReactSerializerState } from "./types";
import { Reconciler } from "../react/reconcilation.js";
import { valueIsClassComponent, convertSimpleClassComponentToFunctionalComponent } from "../react/utils.js";
import { createReactBytecodeTree } from "../react/bytecode.js";
import * as t from "babel-types";

export class Functions {
  constructor(realm: Realm, functions: ?Array<string>, moduleTracer: ModuleTracer) {
    this.realm = realm;
    this.functions = functions;
    this.moduleTracer = moduleTracer;
    this.writeEffects = new Map();
    this.reactBytecodeTrees = new Map();
    this.functionExpressions = new Map();
  }

  realm: Realm;
  functions: ?Array<string>;
  // maps back from FunctionValue to the expression string
  functionExpressions: Map<FunctionValue, string>;
  moduleTracer: ModuleTracer;
  writeEffects: Map<FunctionValue, AdditionalFunctionEffects>;
  reactBytecodeTrees: Map<FunctionValue, ReactBytecodeTree>;

  _generateAdditionalFunctionCallsFromInput(): Array<[FunctionValue, BabelNodeCallExpression]> {
    // lookup functions
    let calls = [];
    for (let fname of this.functions || []) {
      let fun;
      let fnameAst = buildTemplate(fname)({}).expression;
      if (fnameAst) {
        try {
          let e = ignoreErrorsIn(this.realm, () => this.realm.evaluateNodeForEffectsInGlobalEnv(fnameAst));
          fun = e ? e[0] : undefined;
        } catch (ex) {
          if (!(ex instanceof ThrowCompletion)) throw ex;
        }
      }
      if (!(fun instanceof FunctionValue)) {
        let error = new CompilerDiagnostic(
          `Additional function ${fname} not defined in the global environment`,
          null,
          "PP1001",
          "FatalError"
        );
        this.realm.handleError(error);
        throw new FatalError();
      }
      this.functionExpressions.set(fun, fname);
      let call = t.callExpression(fnameAst, []);
      calls.push([fun, call]);
    }
    return calls;
  }

  __generateAdditionalFunctions(globalKey: string) {
    let recordedAdditionalFunctions: Map<FunctionValue, string> = new Map();
    let realm = this.realm;
    let globalRecordedAdditionalFunctionsMap = this.moduleTracer.modules.logger.tryQuery(
      () => Get(realm, realm.$GlobalObject, globalKey),
      realm.intrinsics.undefined,
      false
    );
    invariant(globalRecordedAdditionalFunctionsMap instanceof ObjectValue);
    for (let funcId of globalRecordedAdditionalFunctionsMap.getOwnPropertyKeysArray()) {
      let property = globalRecordedAdditionalFunctionsMap.properties.get(funcId);
      if (property) {
        let funcValue = property.descriptor && property.descriptor.value;
        if (!(funcValue instanceof FunctionValue)) {
          invariant(funcValue instanceof AbstractValue);
          realm.handleError(
            new CompilerDiagnostic(
              `Additional Function Value ${funcId} is an AbstractValue which is not allowed`,
              undefined,
              "PP0001",
              "FatalError"
            )
          );
          throw new FatalError("Additional Function values cannot be AbstractValues");
        }
        recordedAdditionalFunctions.set(funcValue, funcId);
      }
    }
    return recordedAdditionalFunctions;
  }

  _createAdditionalEffects(effects: Effects): AdditionalFunctionEffects {
    return {
      effects,
      transforms: [],
    };
  }

  checkReactRootComponents(statistics: ReactStatistics, react: ReactSerializerState): void {
    let recordedReactRootComponents = this.__generateAdditionalFunctions("__reactComponentRoots");

    // Get write effects of the components
    for (let [componentType] of recordedReactRootComponents) {
      let simpleClassComponents = new Set();
      let reconciler = new Reconciler(this.realm, this.moduleTracer, statistics, react, simpleClassComponents);
      invariant(
        componentType instanceof ECMAScriptSourceFunctionValue,
        "only ECMAScriptSourceFunctionValue function values are supported as React root components"
      );

      // If we're serializing to JSX or createElement, we want to serialize back to
      // an additionalFunction. If we're serializaing to bytecode, we want to serialize
      // out many functions and an array with all the bytecodes/references/strings in
      let effects = reconciler.render(componentType);

      if (this.realm.react.output === "bytecode") {
        let reactBytecodeTree = createReactBytecodeTree(this.realm, componentType, effects, simpleClassComponents);
        this.reactBytecodeTrees.set(componentType, ((reactBytecodeTree: any): ReactBytecodeTree));
      } else {
        let additionalFunctionEffects = this._createAdditionalEffects(((effects: any): Effects));
        invariant(effects[0] instanceof Value);
        if (simpleClassComponents.has(effects[0])) {
          // if the root component was a class and is now simple, we can convert it from a class
          // component to a functional component
          convertSimpleClassComponentToFunctionalComponent(this.realm, componentType, additionalFunctionEffects);
          this.writeEffects.set(componentType, additionalFunctionEffects);
        } else if (valueIsClassComponent(this.realm, componentType)) {
          let prototype = Get(this.realm, componentType, "prototype");
          invariant(prototype instanceof ObjectValue);
          let renderMethod = Get(this.realm, prototype, "render");
          invariant(renderMethod instanceof ECMAScriptSourceFunctionValue);
          this.writeEffects.set(renderMethod, additionalFunctionEffects);
        } else {
          this.writeEffects.set(componentType, additionalFunctionEffects);
        }
      }
    }
  }

  _generateAdditionalFunctionCallsFromDirective(): Array<[FunctionValue, BabelNodeCallExpression]> {
    let recordedAdditionalFunctions = this.__generateAdditionalFunctions("__additionalFunctions");

    // The additional functions we registered at runtime are recorded at:
    // global.__additionalFunctions.id
    let calls = [];
    for (let [funcValue, funcId] of recordedAdditionalFunctions) {
      // TODO #987: Make Additional Functions work with arguments
      calls.push([
        funcValue,
        t.callExpression(
          t.memberExpression(
            t.memberExpression(t.identifier("global"), t.identifier("__additionalFunctions")),
            t.identifier(funcId)
          ),
          []
        ),
      ]);
    }
    return calls;
  }

  checkThatFunctionsAreIndependent() {
    let calls = this._generateAdditionalFunctionCallsFromInput().concat(
      this._generateAdditionalFunctionCallsFromDirective()
    );

    // Get write effects of the functions
    for (let [funcValue, call] of calls) {
      // This may throw a FatalError if there is an unrecoverable error in the called function
      // When that happens we cannot prepack the bundle.
      // There may also be warnings reported for errors that happen inside imported modules that can be postponed.

      let effects = this.realm.evaluatePure(() =>
        this.realm.evaluateNodeForEffectsInGlobalEnv(
          call,
          this.moduleTracer,
          `additional function(${funcValue.getName()})`
        )
      );
      let additionalFunctionEffects = this._createAdditionalEffects(effects);
      this.writeEffects.set(funcValue, additionalFunctionEffects);
    }

    // check that functions are independent
    let conflicts: Map<BabelNodeSourceLocation, CompilerDiagnostic> = new Map();
    for (let [fun1, call1] of calls) {
      // Also do argument validation here
      let funcLength = fun1.getLength();
      if (funcLength && funcLength > 0) {
        // TODO #987: Make Additional Functions work with arguments
        throw new FatalError("TODO: implement arguments to additional functions");
      }
      let additionalFunctionEffects = this.writeEffects.get(fun1);
      invariant(additionalFunctionEffects !== undefined);
      let e1 = additionalFunctionEffects.effects;
      invariant(e1 !== undefined);
      let fun1Name = this.functionExpressions.get(fun1) || fun1.intrinsicName || "unknown";
      if (e1[0] instanceof Completion) {
        let error = new CompilerDiagnostic(
          `Additional function ${fun1Name} may terminate abruptly`,
          e1[0].location,
          "PP1002",
          "FatalError"
        );
        this.realm.handleError(error);
        throw new FatalError();
      }
      for (let [, call2] of calls) {
        if (call1 === call2) continue;
        this.reportWriteConflicts(fun1Name, conflicts, e1[3], call1, call2);
      }
    }
    if (conflicts.size > 0) {
      for (let diagnostic of conflicts.values()) this.realm.handleError(diagnostic);
      throw new FatalError();
    }
  }

  getAdditionalFunctionValuesToEffects(): Map<FunctionValue, AdditionalFunctionEffects> {
    return this.writeEffects;
  }

  getReactBytecodeTrees(): Map<FunctionValue, ReactBytecodeTree> {
    return this.reactBytecodeTrees;
  }

  reportWriteConflicts(
    fname: string,
    conflicts: Map<BabelNodeSourceLocation, CompilerDiagnostic>,
    pbs: PropertyBindings,
    call1: BabelNodeCallExpression,
    call2: BabelNodeCallExpression
  ) {
    let reportConflict = (location: BabelNodeSourceLocation) => {
      let error = new CompilerDiagnostic(
        `Property access conflicts with write in additional function ${fname}`,
        location,
        "PP1003",
        "FatalError"
      );
      conflicts.set(location, error);
    };
    let writtenObjects: Set<ObjectValue | AbstractObjectValue> = new Set();
    pbs.forEach((val, key, m) => {
      writtenObjects.add(key.object);
    });
    let oldReportObjectGetOwnProperties = this.realm.reportObjectGetOwnProperties;
    this.realm.reportObjectGetOwnProperties = (ob: ObjectValue) => {
      let location = this.realm.currentLocation;
      invariant(location);
      if (writtenObjects.has(ob) && !conflicts.has(location)) reportConflict(location);
    };
    let oldReportPropertyAccess = this.realm.reportPropertyAccess;
    this.realm.reportPropertyAccess = (pb: PropertyBinding) => {
      let location = this.realm.currentLocation;
      if (!location) return; // happens only when accessing an additional function property
      if (pbs.has(pb) && !conflicts.has(location)) reportConflict(location);
    };
    try {
      ignoreErrorsIn(this.realm, () => this.realm.evaluateNodeForEffectsInGlobalEnv(call2, this.moduleTracer));
    } finally {
      this.realm.reportPropertyAccess = oldReportPropertyAccess;
      this.realm.reportObjectGetOwnProperties = oldReportObjectGetOwnProperties;
    }
  }
}
