/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { Realm } from "../../realm.js";

import { FunctionValue, NativeFunctionValue } from "../../values/index.js";
import initializeDocument from "./document.js";
import initializeConsole from "../common/console.js";
import { FatalError } from "../../errors.js";
import invariant from "../../invariant.js";
import { TypesDomain, ValuesDomain } from "../../domains/index.js";

export default function(realm: Realm): void {
  let global = realm.$GlobalObject;

  global.$DefineOwnProperty("console", {
    value: initializeConsole(realm),
    writable: true,
    enumerable: false,
    configurable: true,
  });

  global.$DefineOwnProperty("self", {
    value: global,
    writable: true,
    enumerable: true,
    configurable: true,
  });

  global.$DefineOwnProperty("window", {
    value: global,
    writable: true,
    enumerable: true,
    configurable: true,
  });

  global.$DefineOwnProperty("document", {
    value: initializeDocument(realm),
    writable: true,
    enumerable: false,
    configurable: true,
  });

  global.$DefineOwnProperty("setTimeout", {
    value: new NativeFunctionValue(realm, "global.setTimeout", "", 2, (context, args) => {
      let callback = args[0].throwIfNotConcrete();
      if (!(callback instanceof FunctionValue))
        throw realm.createErrorThrowCompletion(realm.intrinsics.TypeError, "callback arguments must be function");
      if (!realm.useAbstractInterpretation) throw new FatalError("TODO #1003: implement global.setTimeout");
      invariant(realm.generator !== undefined);
      let generator = realm.generator;
      return generator.emitCallAndCaptureResult(
        TypesDomain.topVal,
        ValuesDomain.topVal,
        () => generator.preludeGenerator.memoizeReference("global.setTimeout"),
        args
      );
    }),
    writable: true,
    enumerable: true,
    configurable: true,
  });

  global.$DefineOwnProperty("clearTimeout", {
    value: new NativeFunctionValue(realm, "global.clearTimeout", "", 2, (context, args) => {
      if (!realm.useAbstractInterpretation) throw new FatalError("TODO #1003: implement global.clearTimeout");
      invariant(realm.generator !== undefined);
      let generator = realm.generator;
      generator.emitCall(() => generator.preludeGenerator.memoizeReference("global.clearTimeout"), args);
      return realm.intrinsics.undefined;
    }),
    writable: true,
    enumerable: true,
    configurable: true,
  });

  global.$DefineOwnProperty("setInterval", {
    value: new NativeFunctionValue(realm, "global.setInterval", "", 2, (context, args) => {
      if (!realm.useAbstractInterpretation) throw new FatalError("TODO #1003: implement global.setInterval");
      let callback = args[0].throwIfNotConcrete();
      if (!(callback instanceof FunctionValue))
        throw realm.createErrorThrowCompletion(realm.intrinsics.TypeError, "callback arguments must be function");
      invariant(realm.generator !== undefined);
      let generator = realm.generator;
      return generator.emitCallAndCaptureResult(
        TypesDomain.topVal,
        ValuesDomain.topVal,
        () => generator.preludeGenerator.memoizeReference("global.setInterval"),
        args
      );
    }),
    writable: true,
    enumerable: true,
    configurable: true,
  });

  global.$DefineOwnProperty("clearInterval", {
    value: new NativeFunctionValue(realm, "global.clearInterval", "", 2, (context, args) => {
      if (!realm.useAbstractInterpretation) throw new FatalError("TODO #1003: implement global.clearInterval");
      invariant(realm.generator !== undefined);
      let generator = realm.generator;
      generator.emitCall(() => generator.preludeGenerator.memoizeReference("global.clearInterval"), args);
      return realm.intrinsics.undefined;
    }),
    writable: true,
    enumerable: true,
    configurable: true,
  });
}
