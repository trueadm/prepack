/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { DeclarativeEnvironmentRecord, GlobalEnvironmentRecord, LexicalEnvironment } from "../environment.js";
import type { Realm } from "../realm.js";
import {
  AbstractObjectValue,
  AbstractValue,
  ArrayValue,
  BoundFunctionValue,
  ConcreteValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  ObjectValue,
  PrimitiveValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import { Get } from "../methods/index.js";
import { Functions, Materialize, Properties, Utils } from "../singletons.js";
import { isReactElement } from "./utils.js";
import { cloneDescriptor, PropertyDescriptor } from "../descriptors.js";
import * as t from "@babel/types";
import traverse from "@babel/traverse";

function collectAllRenderValuesFromConcreteResult(
  realm: Realm,
  val: ConcreteValue,
  funcEffects: Effects,
  renderValues: Set<Value>,
  insideObject: boolean
): void {
  if (val instanceof ObjectValue) {
    if (isReactElement(val) || ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      renderValues.add(val);
    }
    if (val instanceof FunctionValue && !insideObject) {
      let compilerFlag = Get(realm, val, "name");
      invariant(
        compilerFlag !== realm.intrinsics.undefined,
        `React function call outlining failed. Found ${val.__originalName || "anonymous"} component at line: ${
          val.expressionLocation.start.line
        }.\nEnsure component is a named function and not an anonymous one.`
      );
      renderValues.add(val);
    }

    for (let [propName, binding] of val.properties) {
      if (binding && binding.descriptor) {
        // TODO support prototypes and callee
        if (propName === "callee" || propName === "prototype") {
          // Given we don't support cloning functions now, we only check this for other objects
          if (val instanceof FunctionValue) {
            continue;
          }
          invariant(false, "TODO support prototype and callee for non-function objects");
        }
        invariant(val instanceof ObjectValue);
        let propVal = Get(realm, val, propName);
        collectAllRenderValuesFromResult(realm, propVal, funcEffects, renderValues, true);
      }
    }
  }
}

function collectAllRenderValuesFromAbstractResult(
  realm: Realm,
  val: AbstractValue,
  funcEffects: Effects,
  renderValues: Set<Value>,
  insideObject: boolean
): void {
  if (val.args.length > 0) {
    for (let arg of val.args) {
      collectAllRenderValuesFromResult(realm, arg, funcEffects, renderValues, insideObject);
    }
  } else if (val instanceof AbstractObjectValue && !val.values.isTop()) {
    let elements = Array.from(val.values.getElements());
    if (elements.length === 1) {
      collectAllRenderValuesFromResult(realm, elements[0], funcEffects, renderValues, insideObject);
    }
  }
}

function collectAllRenderValuesFromResult(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  renderValues: Set<Value>,
  insideObject: boolean
): void {
  if (val instanceof ConcreteValue) {
    collectAllRenderValuesFromConcreteResult(realm, val, funcEffects, renderValues, insideObject);
  } else if (val instanceof AbstractValue) {
    collectAllRenderValuesFromAbstractResult(realm, val, funcEffects, renderValues, insideObject);
  }
}

function shouldCloneConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  funcEffects: Effects,
  skipUnknownAbstractProperties: boolean
): void {
  if (val instanceof PrimitiveValue) {
    return true;
  } else if (val instanceof ObjectValue) {
    if (!funcEffects.createdObjects.has(val)) {
      return true;
    }
    for (let [propName, binding] of val.properties) {
      if (binding && binding.descriptor) {
        // TODO support prototypes and callee
        if (propName === "callee" || propName === "prototype") {
          // Given we don't support cloning functions now, we only check this for other objects
          if (val instanceof FunctionValue) {
            continue;
          }
          invariant(false, "TODO support prototype and callee for non-function objects");
        }
        invariant(val instanceof ObjectValue);
        let propVal = Get(realm, val, propName);
        let shouldClone = shouldCloneValue(realm, propVal, funcEffects, skipUnknownAbstractProperties);
        if (!shouldClone) {
          if (propVal instanceof AbstractValue && skipUnknownAbstractProperties) {
            return true;
          }
          return false;
        }
      }
    }
  }
  return true;
}

function shouldCloneAbstractValue(
  realm: Realm,
  val: AbstractValue,
  funcEffects: Effects,
  skipUnknownAbstractProperties: boolean
): void {
  if (!funcEffects.createdAbstracts.has(val)) {
    return true;
  }
  if (val.args.length > 0) {
    for (let arg of val.args) {
      let shouldClone = shouldCloneValue(realm, arg, funcEffects, skipUnknownAbstractProperties);
      if (!shouldClone) {
        return false;
      }
    }
    return true;
  }
  if (val instanceof AbstractObjectValue && !val.values.isTop()) {
    return true;
  }
  if (val.isTemporal() || val.kind === "outlined abstract intrinsic") {
    return false;
  }
}

function shouldCloneValue(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  skipUnknownAbstractProperties: boolean
): void {
  if (val instanceof ConcreteValue) {
    return shouldCloneConcreteValue(realm, val, funcEffects, skipUnknownAbstractProperties);
  } else if (val instanceof AbstractValue) {
    return shouldCloneAbstractValue(realm, val, funcEffects, skipUnknownAbstractProperties);
  }
  invariant(false, "unknown value type found in getOutliningValues");
}

export function possiblyOutlineFunctionCall(
  realm: Realm,
  F: FunctionValue,
  thisValue: Value,
  argsList: Array<Value>,
  originalEffects: Effects
): Value {
  let result = originalEffects.result;
  if (result instanceof AbruptCompletion) {
    debugger;
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    debugger;
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  invariant(result instanceof Value);
  const inlineFunctionCall = () => {
    realm.applyEffects(originalEffects);
    return realm.returnOrThrowCompletion(originalEffects.result);
  };
  let resultIsPrimitive = result instanceof PrimitiveValue;
  let usesThis = thisValue !== realm.intrinsics.undefined;
  let generator = originalEffects.generator;
  let allArgsArePrimitive = argsList.every(arg => arg instanceof PrimitiveValue);
  let notGeneratorEntriesCreated = generator._entries.length === 0;

  if (
    usesThis ||
    allArgsArePrimitive ||
    resultIsPrimitive ||
    F instanceof BoundFunctionValue ||
    notGeneratorEntriesCreated ||
    !Utils.areEffectsPure(realm, originalEffects, F)
  ) {
    return inlineFunctionCall();
  }
  let shouldClone = false;

  realm.withEffectsAppliedInGlobalEnv(() => {
    shouldClone = shouldCloneValue(realm, result, originalEffects, true);
    return null;
  }, originalEffects);

  for (let arg of argsList) {
    if (arg instanceof ObjectValue) {
      // Materialize.materializeObject(realm, arg);
    }
  }
  let marker = AbstractValue.createOutlinedFunctionMarker(realm, F, argsList, originalEffects);

  if (shouldClone) {
    return createModelledValueFromValue(realm, result, marker.intrinsicName, originalEffects);
  }

  return marker;
}

function applyPostValueConfig(realm: Realm, value: Value, clonedValue: Value, intrinsicName: string): void {
  if (value instanceof ObjectValue && clonedValue instanceof ObjectValue) {
    if (realm.react.reactProps.has(value)) {
      realm.react.reactProps.add(clonedValue);
    }
    if (value.isPartialObject()) {
      clonedValue.makePartial();
    }
    if (value.isSimpleObject()) {
      clonedValue.makeSimple();
    }
    if (value.mightBeFinalObject()) {
      clonedValue.makeFinal();
    }
    clonedValue.isScopedTemplate = true;
    clonedValue.intrinsicNameGenerated = true;
  }
  clonedValue.intrinsicName = intrinsicName;
}

function cloneAndModelObjectPropertyDescriptor(
  realm: Realm,
  object: ObjectValue,
  intrinsicName: null | string,
  clonedObject: ObjectValue,
  desc: PropertyDescriptor,
  effects: Effects,
  inReactElement: boolean
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, intrinsicName, effects, inReactElement);
    clonedDesc.value = clonedValue;
  } else {
    invariant(false, "// TODO handle get/set in cloneAndModelObjectPropertyDescriptor");
  }
  return clonedDesc;
}

function isPositiveInteger(str: string) {
  let n = Math.floor(Number(str));
  return n !== Infinity && String(n) === str && n >= 0;
}

function cloneObjectProperties(
  realm: Realm,
  clonedObject: ObjectValue,
  val: ObjectValue,
  intrinsicName: null | string,
  effects: Effects,
  inReactElement: boolean
): void {
  clonedObject.refuseSerialization = true;
  // TODO do symbols
  for (let [propName, { descriptor }] of val.properties) {
    if (descriptor === undefined) {
      continue;
    }
    // TODO support prototypes and callee
    if (propName === "prototype" || propName === "callee") {
      invariant(false, "TODO support prototype and callee");
    }
    invariant(descriptor instanceof PropertyDescriptor);
    let propIntrinsicName = `${intrinsicName}${isPositiveInteger(propName) ? `[${propName}]` : `.${propName}`}`;
    let desc = cloneAndModelObjectPropertyDescriptor(
      realm,
      val,
      propIntrinsicName,
      clonedObject,
      descriptor,
      effects,
      inReactElement
    );
    Properties.OrdinaryDefineOwnProperty(realm, clonedObject, propName, desc);
  }
  let unknownProperty = val.unknownProperty;
  if (unknownProperty !== undefined) {
    let desc;
    let key;
    if (unknownProperty.descriptor !== undefined) {
      desc = cloneAndModelObjectPropertyDescriptor(
        realm,
        val,
        null,
        clonedObject,
        unknownProperty.descriptor,
        effects,
        inReactElement
      );
    }
    if (unknownProperty.key !== undefined) {
      key = cloneAndModelValue(realm, unknownProperty.key, null, effects, inReactElement);
    }
    clonedObject.unknownProperty = {
      descriptor: desc,
      key,
      object: clonedObject,
    };
  }
  clonedObject.refuseSerialization = false;
}

function visitName(path: BabelTraversePath, bindings: Set<string>, name: string, read: boolean, write: boolean): void {
  // Is the name bound to some local identifier? If so, we don't need to do anything
  if (path.scope.hasBinding(name, /*noGlobals*/ true)) return;

  // Otherwise, let's record that there's an unbound identifier
  if (read) bindings.add(name);
  if (write) bindings.add(name);
}

let FunctionClosureRefVisitor = {
  ReferencedIdentifier(path: BabelTraversePath, bindings: Set<string>): void {
    let innerName = path.node.name;
    if (innerName === "arguments") {
      bindings.usesArguments = true;
      return;
    }
    visitName(path, bindings, innerName, true, false);
  },
  "AssignmentExpression|UpdateExpression"(path: BabelTraversePath, bindings: Set<string>): void {
    let doesRead = path.node.operator !== "=";
    for (let name in path.getBindingIdentifiers()) {
      visitName(path, bindings, name, doesRead, true);
    }
  },
};

function getBinding(bindingName: string, originalEnv: LexicalEnvironment): null | Binding {
  let env = originalEnv;

  while (env !== null) {
    let envRec = env.environmentRecord;

    if (envRec instanceof DeclarativeEnvironmentRecord) {
      let envBindings = envRec.bindings;

      if (envBindings[bindingName]) {
        return envBindings[bindingName];
      }
    }
    env = env.parent;
  }
  return null;
}

function cloneAndModelFunctionScopeForBindings(
  realm: Realm,
  scope: LexicalEnvironment,
  bindings: Set<string>,
  effects: Effects
) {
  let env = new LexicalEnvironment(realm);
  let dclRec = new DeclarativeEnvironmentRecord(realm);
  env.____LOL = true;
  dclRec.creatingOptimizedFunction = scope.environmentRecord.creatingOptimizedFunction;
  dclRec.____LOL = true;
  dclRec.lexicalEnvironment = env;
  env.environmentRecord = dclRec;
  if (bindings.size > 0) {
    for (let bindingName of bindings) {
      let binding = getBinding(bindingName, scope);
      // If the binding is null then it's in global scope so we don't need to clone
      if (binding !== null) {
        let clonedBinding = Object.assign({}, binding);
        clonedBinding.environment = dclRec;
        clonedBinding.value = cloneAndModelValue(realm, binding.value, binding.name, effects);
        dclRec.bindings[bindingName] = clonedBinding;
      }
    }
  }
  env.parent = scope.parent;
  return env;
}

function cloneAndModelFunctionValue(
  realm: Realm,
  val: ECMAScriptSourceFunctionValue,
  intrinsicName: string,
  effects: Effects
): ECMAScriptSourceFunctionValue {
  let bindings = new Set();
  let body = val.$ECMAScriptCode;
  let params = val.$FormalParameters;

  traverse(
    t.file(t.program([t.expressionStatement(t.functionExpression(null, params, body))])),
    FunctionClosureRefVisitor,
    null,
    bindings
  );
  traverse.cache.clear();
  let clonedScope = cloneAndModelFunctionScopeForBindings(realm, val.$Environment, bindings, effects);
  let clonedFunction = Functions.FunctionCreate(realm, val.$FunctionKind, params, body, clonedScope, val.$Strict);
  applyPostValueConfig(realm, val, clonedFunction, intrinsicName);
  return clonedFunction;
}

function cloneAndModelObjectValue(
  realm: Realm,
  val: ObjectValue,
  intrinsicName: null | string,
  effects: Effects,
  inReactElement: boolean
): ObjectValue {
  if (!effects.createdObjects.has(val)) {
    return val;
  }
  if (val instanceof ArrayValue) {
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    cloneObjectProperties(realm, clonedObject, val, intrinsicName, effects, isReactElement(val));
    applyPostValueConfig(realm, val, clonedObject, intrinsicName);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    // console.log("function");
    // invariant(val.$Prototype === realm.intrinsics.FunctionPrototype);
    // let abstract = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
    // invariant(intrinsicName !== null);
    // abstract.intrinsicName = intrinsicName;
    // return abstract;
    if (val instanceof BoundFunctionValue) {
      let targetFunction = val.$BoundTargetFunction;
      invariant(targetFunction instanceof ECMAScriptSourceFunctionValue);
      let clonedTargetFunction = cloneAndModelFunctionValue(realm, targetFunction, intrinsicName, effects);
      let clonedBoundFunction = Functions.BoundFunctionCreate(
        realm,
        clonedTargetFunction,
        val.$BoundThis,
        val.$BoundArguments
      );
      return clonedBoundFunction;
    } else if (val instanceof ECMAScriptSourceFunctionValue) {
      return cloneAndModelFunctionValue(realm, val, intrinsicName, effects);
    }
    invariant(false, "should never get here");
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  cloneObjectProperties(realm, clonedObject, val, intrinsicName, effects);
  applyPostValueConfig(realm, val, clonedObject, intrinsicName);
  return clonedObject;
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  intrinsicName: null | string,
  effects: Effects,
  inReactElement: boolean
): ObjectValue {
  if (!effects.createdAbstracts.has(val)) {
    return val;
  }
  const kind = val.kind;
  if (kind === undefined && val instanceof AbstractObjectValue && !val.values.isTop()) {
    let elements = Array.from(val.values.getElements());
    if (elements.length === 1) {
      let clonedTemplate = cloneAndModelValue(realm, elements[0], null, effects);
      return AbstractValue.createAbstractObject(realm, intrinsicName, clonedTemplate);
    } else {
      debugger;
    }
  } else if (kind === "widened numeric property") {
    let clonedVal = AbstractValue.createFromType(realm, Value, "widened numeric property", [...val.args]);
    return clonedVal;
  } else if (kind === "outlined function marker" && inReactElement) {
    debugger;
  } else if (kind === "conditional") {
    // The abstract might contain render values, such as functions or ReactElements
    let renderValues = new Set();
    collectAllRenderValuesFromResult(realm, val, effects, renderValues);
    if (renderValues.size > 0) {
      let renderValuesToJoin = Array.from(renderValues);
      let condIntrinsicName = "__REACT_ARR__" + x++;
      return joinRenderValuesAsConditional(realm, condIntrinsicName, renderValuesToJoin, effects);
    }
  }

  let abstract = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
  invariant(intrinsicName !== null);
  abstract.intrinsicName = intrinsicName;
  return abstract;
}

function cloneAndModelValue(
  realm: Realm,
  val: Value,
  intrinsicName: string,
  effects: Effects,
  inReactElement: boolean
): Value {
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, intrinsicName, effects);
    }
  } else if (val instanceof AbstractValue) {
    return cloneAndModelAbstractValue(realm, val, intrinsicName, effects);
  }
  invariant(false, "cloneValue was passed an unknown type of cloneValue");
}

function createModelledValueFromValue(
  realm: Realm,
  value: Value,
  intrinsicName: null | string,
  effects: Effects
): Value {
  let cloneAndModeledValue;
  let modelledEffects;
  let modelFunc = () => {
    modelledEffects = realm.evaluateForEffects(
      () => {
        cloneAndModeledValue = cloneAndModelValue(realm, value, intrinsicName, effects, false);

        return realm.intrinsics.undefined;
      },
      undefined,
      "createAbstractTemporalValue"
    );
    return null;
  };

  if (effects.canBeApplied) {
    realm.withEffectsAppliedInGlobalEnv(modelFunc, effects);
  } else {
    modelFunc();
  }
  invariant(cloneAndModeledValue instanceof Value);
  realm.applyEffects(modelledEffects);
  return cloneAndModeledValue;
}

var x = 0;

export function getModelledRenderValuesFromMarker(realm: Realm, marker: AbstractValue): Value {
  let markerData = realm.react.outlinedFunctionMarkerData.get(marker);
  invariant(markerData !== undefined);
  let { effects, result } = markerData;
  let modelledValueOrMarker = marker;
  let modelledEffects;
  let modelFunc = () => {
    modelledEffects = realm.evaluateForEffects(
      () => {
        let renderValues = new Set();
        collectAllRenderValuesFromResult(realm, result, effects, renderValues);
        if (renderValues.size > 0) {
          let renderValuesToJoin = Array.from(renderValues);
          let intrinsicName = "__REACT_ARR__" + x++;
          modelledValueOrMarker = joinRenderValuesAsConditional(realm, intrinsicName, renderValuesToJoin, effects);
        }
        return realm.intrinsics.undefined;
      },
      undefined,
      "createAbstractTemporalValue"
    );
    return null;
  };
  realm.withEffectsAppliedInGlobalEnv(modelFunc, effects);
  invariant(modelledValueOrMarker instanceof Value);
  realm.applyEffects(modelledEffects);
  return modelledValueOrMarker;
}

function joinRenderValuesAsConditional(
  realm: Realm,
  intrinsicName: string,
  renderValuesToJoin: Array<Value>,
  effects: Effects
): AbstractValue {
  let condition = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
  condition.intrinsicName = "__REACT_VALUE_COND__" + x++;
  let renderValue = renderValuesToJoin.pop();
  if (renderValue instanceof ConcreteValue) {
    renderValue = createModelledValueFromValue(realm, renderValue, intrinsicName, effects);
  }
  if (renderValuesToJoin.length === 0) {
    let abstract = AbstractValue.createFromType(realm, Value, "outlined abstract intrinsic", []);
    abstract.intrinsicName = intrinsicName;
    return AbstractValue.createFromConditionalOp(realm, condition, renderValue, abstract);
  }
  return AbstractValue.createFromConditionalOp(
    realm,
    condition,
    renderValue,
    joinRenderValuesAsConditional(realm, intrinsicName, renderValuesToJoin, effects)
  );
}
