/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow strict-local */

import { Realm } from "../realm.js";
import {
  AbruptCompletion,
  JoinedNormalAndAbruptCompletions,
  SimpleNormalCompletion,
  Completion,
} from "../completions.js";
import { DeclarativeEnvironmentRecord, GlobalEnvironmentRecord, LexicalEnvironment } from "../environment.js";
import {
  AbstractObjectValue,
  AbstractValue,
  ArrayValue,
  ConcreteValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  NativeFunctionValue,
  ObjectValue,
  PrimitiveValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { type WriteEffects } from "../serializer/types.js";
import { getInitialProps } from "./components.js";
import { getValueFromFunctionCall, valueIsKnownReactAbstraction } from "./utils.js";
import { ReactModelingFailure } from "./errors.js";
import { Get } from "../methods/get.js";
import { Create, Environment, Properties } from "../singletons.js";
import { createAdditionalEffects } from "../serializer/utils.js";
import traverse from "@babel/traverse";
import * as t from "@babel/types";
import { ValuesDomain } from "../domains/index.js";
import { createOperationDescriptor } from "../utils/generator.js";

function getValueAndEffectsFromFunctionCall(
  realm: Realm,
  inGlobalEnv: boolean,
  func: () => Value | Completion
): [Effects, Value] {
  let effects = inGlobalEnv
    ? realm.evaluateForEffectsInGlobalEnv(() => func(), null, "getValueAndEffectsFromFunctionCall")
    : realm.evaluateForEffects(() => func(), null, "getValueAndEffectsFromFunctionCall");
  let result = effects.result;
  if (result instanceof AbruptCompletion) {
    invariant(false, "TODO");
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    invariant(false, "TODO");
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  return [effects, result];
}

function getName(realm: Realm, func: ECMAScriptSourceFunctionValue): string {
  let name = Get(realm, func, "name");
  return name !== realm.intrinsics.undefined ? name.value : func.__originalName || "anonymous function";
}

function visitName(path: BabelTraversePath, bindings: Set<string>, name: string, read: boolean, write: boolean): void {
  // Is the name bound to some local identifier? If so, we don't need to do anything
  if (path.scope.hasBinding(name, /*noGlobals*/ true)) return;

  // Otherwise, let's record that there's an unbound identifier
  if (read || write) bindings.add(name);
}

const FunctionClosureRefVisitor = {
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

function getUnboundBindingsForFunction(func: ECMAScriptSourceFunctionValue): Set<string> {
  let unboundBindings = new Set();
  let body = func.$ECMAScriptCode;
  let params = func.$FormalParameters;

  traverse(
    t.file(t.program([t.expressionStatement(t.functionExpression(null, params, body))])),
    FunctionClosureRefVisitor,
    null,
    unboundBindings
  );
  traverse.cache.clear();
  return unboundBindings;
}

function getBindingValue(realm: Realm, bindingName: string, env: LexicalEnvironment): void | Value {
  let bindingReference = Environment.ResolveBinding(realm, bindingName, true, env);
  let base = bindingReference.base;
  if (base instanceof GlobalEnvironmentRecord) {
    return undefined;
  }
  invariant(base instanceof DeclarativeEnvironmentRecord);
  let binding = base.bindings[bindingName];
  invariant(binding !== undefined);
  let value = binding.value;
  invariant(value instanceof Value);
  return value;
}

function stubObjectProperties(realm: Realm, stub: AbstractValue, stubTemplate: ObjectValue, obj: ObjectValue): void {
  for (let [propName, binding] of obj.properties) {
    if (propName === "caller" || propName === "prototype" || propName === "callee") {
      continue;
    }
    if (binding && binding.descriptor) {
      let propVal = binding.descriptor.value;
      invariant(propVal instanceof Value);
      let intrinsicName = `${stub.intrinsicName}.${propName}`;
      Properties.Set(realm, stubTemplate, propName, stubValue(realm, intrinsicName, propVal), true);
    }
  }
}

function stubFunctionValue(realm: Realm, name: string, func: FunctionValue): FunctionValue {
  let stubFunc = AbstractValue.createTemporalFromBuildFunction(
    realm,
    FunctionValue,
    [func],
    createOperationDescriptor("REACT_MOCK"),
    { skipInvariant: true, isPure: true }
  );
  stubFunc.kind = "stub function";
  stubFunc.$StubFunction = new NativeFunctionValue(
    realm,
    undefined,
    name,
    func.$FormalParameters.length,
    (context, args) => {
      return AbstractValue.createTemporalFromBuildFunction(
        realm,
        Value,
        [func, ...args],
        createOperationDescriptor("REACT_TEMPORAL_FUNC"),
        { skipInvariant: true, isPure: true }
      );
    }
  );
  let template = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  stubObjectProperties(realm, stubFunc, template, func);
  stubFunc.values = new ValuesDomain(template);
  return stubFunc;
}

function stubObjectValue(realm, name: string, obj: ObjectValue): ObjectValue {
  let stubObj = AbstractValue.createTemporalFromBuildFunction(
    realm,
    ObjectValue,
    [obj],
    createOperationDescriptor("REACT_MOCK"),
    { skipInvariant: true, isPure: true }
  );
  let template = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  stubObjectProperties(realm, stubObj, template, obj);
  stubObj.values = new ValuesDomain(template);
  return stubObj;
}

function stubAbstractValue(realm, name: string, abstract: AbstractValue): ObjectValue {
  let stubAbstract = AbstractValue.createTemporalFromBuildFunction(
    realm,
    abstract.getType(),
    [abstract],
    createOperationDescriptor("REACT_MOCK")
  );
  if (stubAbstract instanceof AbstractObjectValue) {
    let template = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
    stubAbstract.values = new ValuesDomain(template);
    template.intrinsicName = stubAbstract.intrinsicName;
    template.intrinsicNameGenerated = true;
    stubAbstract.makePartial();
    stubAbstract.makeSimple("transitive");
  }
  return stubAbstract;
}

function stubValue(realm: Realm, name: string, value: Value): Value {
  if (value instanceof FunctionValue) {
    return stubFunctionValue(realm, name, value);
  } else if (value instanceof ObjectValue) {
    return stubObjectValue(realm, name, value);
  } else if (value instanceof AbstractValue) {
    return stubAbstractValue(realm, name, value);
  }
  return value;
}

function createWidenedEnvForFunctionComponent(realm: Realm, func: ECMAScriptSourceFunctionValue): LexicalEnvironment {
  let originalEnv = func.$Environment;
  let originalEnvRecord = func.$Environment.environmentRecord;
  let unboundBindings = getUnboundBindingsForFunction(func);
  let env = new LexicalEnvironment(realm);
  let dclRec = new DeclarativeEnvironmentRecord(realm);
  dclRec.creatingOptimizedFunction = originalEnvRecord.creatingOptimizedFunction;
  dclRec.lexicalEnvironment = env;
  env.environmentRecord = dclRec;
  env.parent = originalEnv.parent;

  for (let bindingName of unboundBindings) {
    let bindingValue = getBindingValue(realm, bindingName, originalEnv);
    if (bindingValue === undefined) {
      continue;
    }
    dclRec.CreateMutableBinding(bindingName, false, false);
    dclRec.InitializeBinding(bindingName, stubValue(realm, bindingName, bindingValue), true);
  }
  return env;
}

function deeplyCheckIfConditionalBranchHasTemplateValues(realm: Realm, val: Value): boolean {
  if (val instanceof ConcreteValue) {
    return true;
  }
  invariant(val instanceof AbstractValue);
  if (valueIsKnownReactAbstraction(realm, val)) {
    return true;
  }
  if (val.kind === "conditional" || val.kind === "||" || val.kind === "&&") {
    for (let arg of val.args) {
      let check = deeplyCheckIfConditionalBranchHasTemplateValues(realm, arg);
      if (check) {
        return true;
      }
    }
  }
  return false;
}

function collectRuntimeValuesNeededForReactTemplateFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  runtimeValues: Set<Value>
): void {
  if (val instanceof PrimitiveValue) {
    return; // We don't need to mark primitve values
  }
  invariant(val instanceof ObjectValue);
  if (val.isPartialObject() && !realm.react.reactProps.has(val)) {
    invariant(false, "TODO");
  }
  if (val.mightBeLeakedObject()) {
    // We probably have to mark the runtime value
    invariant(false, "TODO");
  }
  for (let [propName, binding] of val.properties) {
    if (binding && binding.descriptor) {
      if (propName === "callee" || propName === "prototype") {
        // Given we don't support cloning functions now, we only check this for other objects
        if (val instanceof FunctionValue) {
          continue;
        }
        invariant(false, "TODO support prototype and callee for non-function objects");
      }
      let propVal = binding.descriptor.value;
      invariant(propVal instanceof Value);
      collectRuntimeValuesNeededForReactTemplateFromValue(realm, propVal, runtimeValues);
    }
  }
  if (val.temporalAlias !== undefined) {
    collectRuntimeValuesNeededForReactTemplateFromValue(realm, val.temporalAlias, runtimeValues);
  }
  // TODO handle unknownProperty
  if (val instanceof FunctionValue) {
    invariant(false, "TODO");
  }
  if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
    invariant(false, "TODO");
  }
}

function collectRuntimeValuesNeededForReactTemplateFromAbstractValue(
  realm: Realm,
  val: AbstractValue,
  runtimeValues: Set<Value>
): void {
  const kind = val.kind;
  if (kind === "conditional") {
    let [condValue, consequentVal, alternateVal] = val.args;
    let consequentHasTemplateValues = deeplyCheckIfConditionalBranchHasTemplateValues(realm, consequentVal);
    let alternateHasTemplateValues = deeplyCheckIfConditionalBranchHasTemplateValues(realm, alternateVal);

    if (!consequentHasTemplateValues && !alternateHasTemplateValues) {
      runtimeValues.add(val);
      return;
    }
    runtimeValues.add(condValue);
    if (consequentHasTemplateValues) {
      collectRuntimeValuesNeededForReactTemplateFromValue(realm, consequentVal, runtimeValues);
    } else {
      runtimeValues.add(consequentVal);
    }
    if (alternateHasTemplateValues) {
      collectRuntimeValuesNeededForReactTemplateFromValue(realm, alternateVal, runtimeValues);
    } else {
      runtimeValues.add(alternateVal);
    }
  } else if (kind === "||" || kind === "&&") {
    debugger;
  } else if (kind === "abstractConcreteUnion") {
    // TODO does this add value?
    runtimeValues.add(val);
  } else if (val.isTemporal()) {
    runtimeValues.add(val);
  } else {
    debugger;
  }
}

function collectRuntimeValuesNeededForReactTemplateFromValue(
  realm: Realm,
  val: Value,
  runtimeValues: Set<Value>
): void {
  if (val instanceof ConcreteValue) {
    collectRuntimeValuesNeededForReactTemplateFromConcreteValue(realm, val, runtimeValues);
  } else if (val instanceof AbstractValue) {
    collectRuntimeValuesNeededForReactTemplateFromAbstractValue(realm, val, runtimeValues);
  }
}

function getReactComponentModelInWidenedEnvironment(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue
): { effects: Effects, tempate: Value, runtimeValuesMap: Map<Value, number> } {
  let runtimeValuesMap = new Map();
  let template;

  let [effects] = getValueAndEffectsFromFunctionCall(realm, true, () => {
    // Model the props object as the first argument for this function
    let thisValue = realm.intrinsics.undefined; // We only deal with function components, so there is no "this"
    let args = [getInitialProps(realm, func, {})]; // We only support props (TODO: need to support forwardRef). No legacy context.
    // Temporarily create a new env for the function that has these bindings marked as abstract values
    let originalEnv = func.$Environment;
    let widenedEnvForFunction = createWidenedEnvForFunctionComponent(realm, func);
    func.$Environment = widenedEnvForFunction;
    try {
      let funcCall = () => getValueFromFunctionCall(realm, func, thisValue, args);
      template = realm.isInPureScope() ? funcCall() : realm.evaluateWithPureScope(funcCall);
    } catch (e) {
      debugger;
      throw new ReactModelingFailure(
        `Failed to evaluate React function component ${getName(realm, func)} due to an error.`
      );
    } finally {
      func.$Environment = originalEnv;
    }

    let runtimeValues = new Set();
    collectRuntimeValuesNeededForReactTemplateFromValue(realm, template, runtimeValues);

    let componentEntryPoint = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
    let reactRuntimeValues = Create.ArrayCreate(realm, runtimeValues.size);

    let index = 0;
    for (let runtimeValue of runtimeValues) {
      Properties.Set(realm, reactRuntimeValues, index + "", runtimeValue, true);
      runtimeValuesMap.set(runtimeValue, index);
      index++;
    }
    Properties.Set(realm, componentEntryPoint, "__reactRuntimeValues", reactRuntimeValues, true);
    return componentEntryPoint;
  });

  return { effects, template, runtimeValuesMap };
}

export function modelReactComponentTreeRoots(realm: Realm, func: FunctionValue, writeEffects: WriteEffects): void {
  invariant(func instanceof ECMAScriptSourceFunctionValue);
  let model = getReactComponentModelInWidenedEnvironment(realm, func);
  let parentOptimizedFunction = realm.currentOptimizedFunction;
  realm.react.reactComponentModels.set(func, model);
  let { effects } = model;
  let modeledFunctionEffects = createAdditionalEffects(
    realm,
    effects,
    false,
    "ReactModeledFunctionEffects",
    func,
    parentOptimizedFunction
  );
  writeEffects.set(func, modeledFunctionEffects);
}
