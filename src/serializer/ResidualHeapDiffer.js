/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { Realm } from "../realm.js";
import { Logger } from "../utils/logger.js";
import { FunctionValue } from "../values/index.js";
import type { AdditionalFunctionEffects } from "./types.js";
import { Generator } from "../utils/generator.js";

export class ResidualHeapDiffer {
  constructor(
    realm: Realm,
    logger: Logger,
    optimizedFunctionValuesAndEffects: Map<FunctionValue, AdditionalFunctionEffects>
  ) {
    this.realm = realm;
    this.logger = logger;
    this.additionalFunctionValuesAndEffects = optimizedFunctionValuesAndEffects;
    this.similarShapeGenerators = new Map();
    this.shapeEquivalenceByEntrySize = new Map();
  }
  realm: Realm;
  logger: Logger;
  optimizedFunctionValuesAndEffects: Map<FunctionValue, AdditionalFunctionEffects>;
  similarShapeGenerators: Map<Generator, any>;
  shapeEquivalenceByEntrySize: Map<number, any>;

  visitRoots(): void {
    this._visitGenerator(this.realm.generator);
  }

  _visitGenerator(generator: Generator) {
    let entries = generator._entries;

    for (let entry of entries) {

    }
    debugger;
  }
}
