/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import * as Values from "./values/index.js";
import { Realm, ExecutionContext } from "./realm.js";
import invariant from "./invariant.js";
import type { InternalPrepackModules } from "./types.js";
import parse from "./utils/parse.js";
import fs from "fs";
import { AbruptCompletion } from "./completions.js";
import { Environment } from "./singletons.js";
import { LexicalEnvironment, ModuleEnvironmentRecord } from "./environment.js";
import { PropertyDescriptor } from "./descriptors.js";

export class ModuleResolver {
  constructor(realm: Realm, internalModules: InternalPrepackModules) {
    this.realm = realm;
    this._transformsForEvent = new Map();
    this.internalModules = internalModules;
  }

  realm: Realm;
  resolveModuleNameFunc: void | (() => string | Value | undefined);
  _transformsForEvent: Map<string, Array<(name: string, sourceOrValue: string | Value) => string | Value>>;
  internalModules: InternalPrepackModules;

  _readModule(modulePath: string) {
    try {
      return fs.readFileSync(modulePath, "utf-8");
    } catch (e) {
      // TODO handle error
    }
  }

  _createEnvironmentForModule(ast): ModuleEnvironmentRecord {
    let moduleEnvironment = new LexicalEnvironment(this.realm, ast);
    let environmentRecord = new ModuleEnvironmentRecord(this.realm);
    moduleEnvironment.environmentRecord = environmentRecord;
    // TODO: e need to scan AST and find all "import" bindings as per spec.
    // See: https://tc39.github.io/ecma262/#module-environment
    moduleEnvironment.parent = this.realm.$GlobalEnv;
    return moduleEnvironment;
  }

  executeModule(
    moduleName: string,
    { entryModulePath, entryModuleSource },
    onParse: void | (BabelNodeFile => void) = undefined
  ): Value {
    let moduleSource = entryModuleSource;
    if (entryModuleSource === undefined) {
      invariant(entryModulePath !== undefined);
      moduleSource = this._readModule(entryModulePath);
    }
    invariant(moduleSource !== undefined);
    moduleSource = this._applyTransforms("module-source", moduleName, moduleSource);
    let ast = this.realm.statistics.parsing.measure(() => parse(this.realm, moduleSource, entryModulePath, "module"));
    if (onParse) onParse(ast);
    let moduleEnvironment = this._createEnvironmentForModule(ast);
    let context = new ExecutionContext();
    context.lexicalEnvironment = moduleEnvironment;
    context.variableEnvironment = moduleEnvironment;
    context.realm = this.realm;
    this.realm.pushContext(context);
    let res;
    try {
      // Modules are always strict mode
      res = this.realm.statistics.evaluation.measure(() => moduleEnvironment.evaluateCompletion(ast, true));
    } finally {
      this.realm.popContext(context);
    }
    if (res instanceof AbruptCompletion) return;
    let value = Environment.GetValue(this.realm, res);
    value = this._applyTransforms("module-value", moduleName, value);
    return value;
  }

  import(moduleName: string): Value | string | symbol | void {
    // Resolve the moduleName to a value or path
    invariant(this.resolveModuleNameFunc !== undefined);
    let resolveAtRuntime = Symbol.for("resolve module at runtime");
    return this.resolveModuleNameFunc(moduleName, resolveAtRuntime, this.internalModules);
  }

  _applyTransforms(eventName: string, moduleName: string, originalInput: string | Value): string {
    let output = originalInput;
    let transformsFuncs = this._transformsForEvent.get(eventName);
    for (let transformFunc of transformsFuncs) {
      output = transformFunc(moduleName, output);
      invariant(output !== undefined, "_applyTransforms failed");
    }
    return output;
  }

  addTransformListener(
    eventName: string,
    transformFunc: (name: string, sourceOrValue: string | Value) => string | Value
  ): void {
    let transformsFuncs = this._transformsForEvent.get(eventName);
    if (transformsFuncs === undefined) {
      transformsFuncs = [];
      this._transformsForEvent.set(eventName, transformsFuncs);
    }
    transformsFuncs.push(transformFunc);
  }
}

export function initializeModuleResolver(
  realm: Realm,
  moduleResolverPath: string,
  internalModules: InternalPrepackModules
): void {
  let resolveModuleNameFunc;
  let bagOfObjects = { ...Values, PropertyDescriptor };
  let moduleResolver = (realm.moduleResolver = new ModuleResolver(realm, internalModules));
  let transformModuleSource = func => moduleResolver.addTransformListener("module-source", func);
  let transformModuleValue = func => moduleResolver.addTransformListener("module-value", func);
  let bagOfTransforms = { transformModuleSource, transformModuleValue };
  try {
    resolveModuleNameFunc = require(moduleResolverPath)(realm, bagOfTransforms, bagOfObjects);
  } catch (e) {
    // TODO handle error
  }
  invariant(typeof resolveModuleNameFunc === "function");
  moduleResolver.resolveModuleNameFunc = resolveModuleNameFunc;
}
