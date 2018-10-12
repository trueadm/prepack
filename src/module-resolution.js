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
  constructor(
    realm: Realm,
    resolveModuleNameFunc: () => string | Value | undefined,
    internalModules: InternalPrepackModules
  ) {
    this.realm = realm;
    this.resolveModuleNameFunc = resolveModuleNameFunc;
    this.internalModules = internalModules;
  }

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

  executeModule({ entryModulePath, entryModuleSource }, onParse: void | (BabelNodeFile => void) = undefined): Value {
    if (entryModuleSource === undefined) {
      invariant(entryModulePath !== undefined);
      entryModuleSource = this._readModule(entryModulePath);
    }
    invariant(entryModulePath !== undefined);
    let ast = this.realm.statistics.parsing.measure(() =>
      parse(this.realm, entryModuleSource, entryModulePath, "module")
    );
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
    return Environment.GetValue(this.realm, res);
  }

  import(moduleName: string) {
    debugger;
  }
}

export function initializeModuleResolver(
  realm: Realm,
  moduleResolverPath: string,
  internalModules: InternalPrepackModules
): void {
  let resolveModuleNameFunc;
  let bagOfObjects = { ...Values, PropertyDescriptor };
  try {
    resolveModuleNameFunc = require(moduleResolverPath)(realm, bagOfObjects);
  } catch (e) {
    // TODO handle error
  }
  invariant(typeof resolveModuleNameFunc === "function");
  realm.moduleResolver = new ModuleResolver(realm, resolveModuleNameFunc, internalModules);
}
