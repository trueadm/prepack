/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { ErrorHandler } from "./errors.js";

export type Compatibility = "browser" | "jsc-600-1-4-17" | "node-source-maps" | "node-cli" | "react-mocks";
export const CompatibilityValues = ["browser", "jsc-600-1-4-17", "node-source-maps", "node-cli"];
export type ReactOutputTypes = "create-element" | "jsx";

export type RealmOptions = {
  compatibility?: Compatibility,
  debugNames?: boolean,
  errorHandler?: ErrorHandler,
  mathRandomSeed?: string,
  omitInvariants?: boolean,
  uniqueSuffix?: string,
  residual?: boolean,
  serialize?: boolean,
  strictlyMonotonicDateNow?: boolean,
  timeout?: number,
  maxStackDepth?: number,
  reactEnabled?: boolean,
  reactOutput?: ReactOutputTypes,
};

export type SerializerOptions = {
  additionalFunctions?: Array<string>,
  lazyObjectsRuntime?: string,
  delayInitializations?: boolean,
  delayUnsupportedRequires?: boolean,
  initializeMoreModules?: boolean,
  internalDebug?: boolean,
  debugScopes?: boolean,
  logStatistics?: boolean,
  logModules?: boolean,
  profile?: boolean,
  inlineExpressions?: boolean,
  simpleClosures?: boolean,
  trace?: boolean,
  heapGraph?: boolean,
};

export type PartialEvaluatorOptions = {
  sourceMaps?: boolean,
};

export type DebuggerOptions = {
  inFilePath: string,
  outFilePath: string,
};

export const defaultOptions = {};
