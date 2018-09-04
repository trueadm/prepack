/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow strict-local */

import { type Effects, Realm } from "../realm.js";
import { AbstractValue, ECMAScriptSourceFunctionValue, ObjectValue, BoundFunctionValue } from "../values/index.js";
import { createAdditionalEffects } from "../serializer/utils.js";
import {
  convertFunctionalComponentToComplexClassComponent,
  convertSimpleClassComponentToFunctionalComponent,
  createNoopFunction,
  createReactEvaluatedNode,
  getComponentName,
  getComponentTypeFromRootValue,
  normalizeFunctionalComponentParamaters,
  valueIsClassComponent,
} from "./utils.js";
import { type WriteEffects, type ReactEvaluatedNode, ReactStatistics } from "../serializer/types.js";
import { Reconciler, type ComponentTreeState } from "./reconcilation.js";
import { ReconcilerFatalError } from "./errors.js";
import { Properties } from "../singletons.js";
import { Get } from "../methods/index.js";
import invariant from "../invariant.js";
import type { ReactComponentTreeConfig } from "../types.js";
import { Logger } from "../utils/logger.js";

function applyWriteEffectsForOptimizedComponent(
  realm: Realm,
  componentType: ECMAScriptSourceFunctionValue | BoundFunctionValue,
  _effects: Effects,
  componentTreeState: ComponentTreeState,
  evaluatedNode: ReactEvaluatedNode,
  writeEffects: WriteEffects,
  environmentRecordIdAfterGlobalCode: number
): void {
  let effects = _effects;
  let additionalFunctionEffects = createAdditionalEffects(
    realm,
    effects,
    false,
    "ReactAdditionalFunctionEffects",
    environmentRecordIdAfterGlobalCode
  );
  if (additionalFunctionEffects === null) {
    throw new ReconcilerFatalError(
      `Failed to optimize React component tree for "${evaluatedNode.name}" due to an unsupported completion`,
      evaluatedNode
    );
  }
  effects = additionalFunctionEffects.effects;
  let value = effects.result;

  if (value === realm.intrinsics.undefined) {
    // if we get undefined, then this component tree failed and a message was already logged
    // in the reconciler
    return;
  }
  if (valueIsClassComponent(realm, componentType)) {
    if (componentTreeState.status === "SIMPLE") {
      // if the root component was a class and is now simple, we can convert it from a class
      // component to a functional component
      if (componentType instanceof BoundFunctionValue) {
        let targetFunction = componentType.$BoundTargetFunction;
        invariant(targetFunction instanceof ECMAScriptSourceFunctionValue);
        convertSimpleClassComponentToFunctionalComponent(realm, targetFunction, additionalFunctionEffects);
        normalizeFunctionalComponentParamaters(targetFunction);
        writeEffects.set(targetFunction, additionalFunctionEffects);
      } else {
        convertSimpleClassComponentToFunctionalComponent(realm, componentType, additionalFunctionEffects);
        normalizeFunctionalComponentParamaters(componentType);
        writeEffects.set(componentType, additionalFunctionEffects);
      }
    } else {
      let prototype = Get(realm, componentType, "prototype");
      invariant(prototype instanceof ObjectValue);
      let renderMethod = Get(realm, prototype, "render");
      invariant(renderMethod instanceof ECMAScriptSourceFunctionValue);
      writeEffects.set(renderMethod, additionalFunctionEffects);
    }
  } else {
    if (componentTreeState.status === "COMPLEX") {
      convertFunctionalComponentToComplexClassComponent(
        realm,
        componentType,
        componentTreeState.componentType,
        additionalFunctionEffects
      );
      let prototype = Get(realm, componentType, "prototype");
      invariant(prototype instanceof ObjectValue);
      let renderMethod = Get(realm, prototype, "render");
      invariant(renderMethod instanceof ECMAScriptSourceFunctionValue);
      writeEffects.set(renderMethod, additionalFunctionEffects);
    } else {
      if (componentType instanceof BoundFunctionValue) {
        let targetFunction = componentType.$BoundTargetFunction;
        invariant(targetFunction instanceof ECMAScriptSourceFunctionValue);
        normalizeFunctionalComponentParamaters(targetFunction);
        writeEffects.set(targetFunction, additionalFunctionEffects);
      } else {
        normalizeFunctionalComponentParamaters(componentType);
        writeEffects.set(componentType, additionalFunctionEffects);
      }
    }
  }
  // apply contextTypes for legacy context
  if (componentTreeState.contextTypes.size > 0) {
    let contextTypes = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
    let noOpFunc = createNoopFunction(realm);
    for (let key of componentTreeState.contextTypes) {
      Properties.Set(realm, contextTypes, key, noOpFunc, true);
    }
    Properties.Set(realm, componentType, "contextTypes", contextTypes, true);
  }
}

function optimizeReactComponentTreeBranches(
  realm: Realm,
  reconciler: Reconciler,
  writeEffects: WriteEffects,
  environmentRecordIdAfterGlobalCode: number,
  logger: Logger,
  alreadyEvaluated: Map<ECMAScriptSourceFunctionValue | BoundFunctionValue, ReactEvaluatedNode>
): void {
  if (realm.react.verbose && reconciler.branchedComponentTrees.length > 0) {
    logger.logInformation(`  Evaluating React component tree branches...`);
  }
  // for now we just use abstract props/context, in the future we'll create a new branch with a new component
  // that used the props/context. It will extend the original component and only have a render method
  for (let { rootValue: branchRootValue, evaluatedNode } of reconciler.branchedComponentTrees) {
    let branchComponentType = getComponentTypeFromRootValue(realm, branchRootValue);
    if (branchComponentType === null) {
      evaluatedNode.status = "UNKNOWN_TYPE";
      continue;
    }
    if (alreadyEvaluated.has(branchComponentType)) {
      return;
    }
    alreadyEvaluated.set(branchComponentType, evaluatedNode);
    reconciler.clearComponentTreeState();
    if (realm.react.verbose) {
      logger.logInformation(`    Evaluating ${evaluatedNode.name} (branch)`);
    }
    let branchEffects = reconciler.resolveReactComponentTree(branchComponentType, null, null, evaluatedNode);
    if (realm.react.verbose) {
      logger.logInformation(`    ✔ ${evaluatedNode.name} (branch)`);
    }
    let branchComponentTreeState = reconciler.componentTreeState;
    applyWriteEffectsForOptimizedComponent(
      realm,
      branchComponentType,
      branchEffects,
      branchComponentTreeState,
      evaluatedNode,
      writeEffects,
      environmentRecordIdAfterGlobalCode
    );
  }
}

export function optimizeReactComponentTreeRoot(
  realm: Realm,
  componentRoot: ECMAScriptSourceFunctionValue | BoundFunctionValue | AbstractValue,
  config: ReactComponentTreeConfig,
  writeEffects: WriteEffects,
  environmentRecordIdAfterGlobalCode: number,
  logger: Logger,
  statistics: ReactStatistics,
  alreadyEvaluated: Map<ECMAScriptSourceFunctionValue | BoundFunctionValue, ReactEvaluatedNode>
): void {
  let reconciler = new Reconciler(realm, config, alreadyEvaluated, statistics, logger);
  let componentType = getComponentTypeFromRootValue(realm, componentRoot);
  if (componentType === null) {
    return;
  }
  if (alreadyEvaluated.has(componentType)) {
    return;
  }
  let evaluatedRootNode = createReactEvaluatedNode("ROOT", getComponentName(realm, componentType));
  statistics.evaluatedRootNodes.push(evaluatedRootNode);
  alreadyEvaluated.set(componentType, evaluatedRootNode);
  if (realm.react.verbose) {
    logger.logInformation(`  Evaluating ${evaluatedRootNode.name} (root)`);
  }
  let componentTreeEffects = reconciler.resolveReactComponentTree(componentType, null, null, evaluatedRootNode);
  if (realm.react.verbose) {
    logger.logInformation(`  ✔ ${evaluatedRootNode.name} (root)`);
  }

  applyWriteEffectsForOptimizedComponent(
    realm,
    componentType,
    componentTreeEffects,
    reconciler.componentTreeState,
    evaluatedRootNode,
    writeEffects,
    environmentRecordIdAfterGlobalCode
  );
  let startingComponentTreeBranches = 0;
  do {
    startingComponentTreeBranches = reconciler.branchedComponentTrees.length;
    optimizeReactComponentTreeBranches(
      realm,
      reconciler,
      writeEffects,
      environmentRecordIdAfterGlobalCode,
      logger,
      alreadyEvaluated
    );
  } while (startingComponentTreeBranches !== reconciler.branchedComponentTrees.length);
}
