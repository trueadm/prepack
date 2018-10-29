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
  BoundFunctionValue,
  ConcreteValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  NativeFunctionValue,
  ObjectValue,
  PrimitiveValue,
  StringValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { type WriteEffects } from "../serializer/types.js";
import { getInitialProps } from "./components.js";
import {
  getIntrinsicNameFromTemporalValueDeeplyReferencingPropsObject,
  getValueFromFunctionCall,
  isTemporalValueDeeplyReferencingKnownObject,
  valueIsKnownReactAbstraction,
} from "./utils.js";
import { ReactModelingFailure } from "./errors.js";
import { Get } from "../methods/get.js";
import { Create, Environment, Functions, Properties, Utils } from "../singletons.js";
import { createAdditionalEffects } from "../serializer/utils.js";
import traverse from "@babel/traverse";
import * as t from "@babel/types";
import { ValuesDomain } from "../domains/index.js";
import { createOperationDescriptor } from "../utils/generator.js";
import { cloneDescriptor, PropertyDescriptor } from "../descriptors.js";

function getValueWithPreviousEffectsApplied(realm, previousEffects, f) {
  let effects;
  let value;
  realm.withEffectsAppliedInGlobalEnv(() => {
    effects = realm.evaluateForEffects(
      () => {
        value = f();
        return realm.intrinsics.undefined;
      },
      undefined,
      "createAbstractTemporalValue"
    );
    f();
    return null;
  }, previousEffects);
  realm.applyEffects(effects);
  return value;
}

function isAbstractValueBinaryExpression(val: AbstractValue): boolean {
  const kind = val.kind;
  return (
    val.args.length === 2 &&
    (kind === "!=" ||
      kind === "==" ||
      kind === "==" ||
      kind === "===" ||
      kind === "!==" ||
      kind === "instanceof" ||
      kind === "in" ||
      kind === ">" ||
      kind === "<" ||
      kind === ">=" ||
      kind === "<=" ||
      kind === ">>>" ||
      kind === ">>" ||
      kind === "<<" ||
      kind === "&" ||
      kind === "|" ||
      kind === "^" ||
      kind === "**" ||
      kind === "%" ||
      kind === "/" ||
      kind === "*" ||
      kind === "+" ||
      kind === "-" ||
      kind === "check for known property")
  );
}

export function isAbstractValueUnaryExpression(val: AbstractValue): boolean {
  const kind = val.kind;
  return (
    val.args.length === 1 &&
    (kind === "+" ||
      kind === "-" ||
      kind === "!" ||
      kind === "typeof" ||
      kind === "delete" ||
      kind === "void" ||
      kind === "~")
  );
}

function isReactMockedLibrary(realm: Realm, value: ObjectValue): boolean {
  const libs = Object.values(realm.fbLibraries);
  for (let lib of libs) {
    if (lib === value) {
      return true;
    }
  }
  return false;
}

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
  if (base instanceof GlobalEnvironmentRecord || base === undefined) {
    return undefined;
  }
  invariant(base instanceof DeclarativeEnvironmentRecord);
  let binding = base.bindings[bindingName];
  invariant(binding !== undefined);
  let value = binding.value;
  invariant(value instanceof Value);
  return value;
}

function stubObjectProperties(
  realm: Realm,
  stub: AbstractValue,
  stubTemplate: ObjectValue,
  obj: ObjectValue,
  writeEffects: WriteEffects
): void {
  for (let [propName, binding] of obj.properties) {
    if (propName === "caller" || propName === "prototype" || propName === "callee") {
      continue;
    }
    if (binding && binding.descriptor) {
      let propVal = binding.descriptor.value;
      invariant(propVal instanceof Value);
      let intrinsicName = `${stub.intrinsicName}.${propName}`;
      Properties.Set(realm, stubTemplate, propName, stubValue(realm, intrinsicName, propVal, writeEffects), true);
    }
  }
}

function stubFunctionValue(realm: Realm, name: string, func: FunctionValue, writeEffects: WriteEffects): FunctionValue {
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
      modelReactComponentInnerFunctionCall(realm, func, writeEffects);
      let val = AbstractValue.createTemporalFromBuildFunction(
        realm,
        Value,
        [func, ...args],
        createOperationDescriptor("REACT_TEMPORAL_FUNC"),
        { skipInvariant: true, isPure: true }
      );
      val.kind = "outlined function call";
      return val;
    }
  );
  let template = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  stubObjectProperties(realm, stubFunc, template, func, writeEffects);
  stubFunc.values = new ValuesDomain(template);
  return stubFunc;
}

function stubObjectValue(realm, name: string, obj: ObjectValue, writeEffects: WriteEffects): ObjectValue {
  let stubObj = AbstractValue.createTemporalFromBuildFunction(
    realm,
    ObjectValue,
    [obj],
    createOperationDescriptor("REACT_MOCK"),
    { skipInvariant: true, isPure: true }
  );
  let template = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  stubObjectProperties(realm, stubObj, template, obj, writeEffects);
  stubObj.values = new ValuesDomain(template);
  return stubObj;
}

function stubAbstractValue(realm, name: string, abstract: AbstractValue): ObjectValue {
  // if (abstract instanceof AbstractObjectValue) {
  //   debugger;
  // }
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

function stubValue(realm: Realm, name: string, value: Value, writeEffects: WriteEffects): Value {
  if (value instanceof FunctionValue) {
    return stubFunctionValue(realm, name, value, writeEffects);
  } else if (value instanceof ObjectValue) {
    if (isReactMockedLibrary(realm, value)) {
      return;
    }
    return stubObjectValue(realm, name, value, writeEffects);
  } else if (value instanceof AbstractValue) {
    return stubAbstractValue(realm, name, value);
  }
  return value;
}

function createWidenedEnvForFunctionComponent(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  writeEffects: WriteEffects
): LexicalEnvironment {
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
    dclRec.InitializeBinding(bindingName, stubValue(realm, bindingName, bindingValue, writeEffects), true);
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
  if (val instanceof AbstractValue && val.kind === "outlined function call") {
    let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
    invariant(temporalOperationEntry !== undefined);
    let [outlinedFunc] = temporalOperationEntry.args;
    if (realm.react.reactOutliningModels.has(outlinedFunc)) {
      return true;
    }
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

function collectRuntimeValuesNeededForReactTemplateFromArrayWithWidenedNumericProperty(
  realm: Realm,
  val: ArrayValue,
  runtimeValues: Set<Value>
): void {
  let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
  invariant(temporalOperationEntry !== undefined);
  let { args } = temporalOperationEntry;
  for (let arg of args) {
    collectRuntimeValuesNeededForReactTemplateFromValue(realm, arg, runtimeValues);
  }
}

function collectRuntimeValuesNeededForReactTemplateFromFunctionValue(
  realm: Realm,
  val: FunctionValue,
  runtimeValues: Set<Value>
): void {
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
  let scope = val.$Environment;
  if (bindings.size > 0) {
    for (let bindingName of bindings) {
      let binding = getBinding(bindingName, scope);
      // If the binding is null then it's in global scope so we don't need to clone
      if (binding !== null && binding.value !== undefined) {
        collectRuntimeValuesNeededForReactTemplateFromValue(realm, binding.value, runtimeValues);
      }
    }
  }
}

function collectRuntimeValuesNeededForReactTemplateFromConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  runtimeValues: Set<Value>
): void {
  if (val instanceof PrimitiveValue || val instanceof NativeFunctionValue) {
    return; // We don't need to mark primitve values
  }
  invariant(val instanceof ObjectValue);
  if (val.isPartialObject() && !realm.react.reactProps.has(val)) {
    invariant(false, "TODO");
  }
  if (val.mightBeLeakedObject()) {
    // We probably have to mark the runtime value
    // invariant(false, "TODO");
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
    collectRuntimeValuesNeededForReactTemplateFromFunctionValue(realm, val, runtimeValues);
  }
  if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
    collectRuntimeValuesNeededForReactTemplateFromArrayWithWidenedNumericProperty(realm, val, runtimeValues);
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
    let [leftVal, rigthVal] = val.args;
    let leftHasTemplateValues = deeplyCheckIfConditionalBranchHasTemplateValues(realm, leftVal);
    let rightHasTemplateValues = deeplyCheckIfConditionalBranchHasTemplateValues(realm, rigthVal);

    if (!leftHasTemplateValues && !rightHasTemplateValues) {
      runtimeValues.add(val);
      return;
    }
    if (leftHasTemplateValues) {
      collectRuntimeValuesNeededForReactTemplateFromValue(realm, leftVal, runtimeValues);
    } else {
      runtimeValues.add(leftVal);
    }
    if (rightHasTemplateValues) {
      collectRuntimeValuesNeededForReactTemplateFromValue(realm, rigthVal, runtimeValues);
    } else {
      runtimeValues.add(rigthVal);
    }
  } else if (kind === "abstractConcreteUnion") {
    // TODO does this add value?
    runtimeValues.add(val);
  } else if (val.isTemporal()) {
    if (val.kind === "outlined function call") {
      let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
      invariant(temporalOperationEntry !== undefined);
      let [, ...args] = temporalOperationEntry.args;
      for (let arg of args) {
        collectRuntimeValuesNeededForReactTemplateFromValue(realm, arg, runtimeValues);
      }
    } else if (val.kind === "stub function") {
      return;
    }
    runtimeValues.add(val);
  } else if (isAbstractValueBinaryExpression(val) || isAbstractValueUnaryExpression(val)) {
    runtimeValues.add(val);
  } else if (kind !== undefined) {
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

function applyPostValueConfig(realm: Realm, value: Value, clonedValue: Value): void {
  if (value instanceof ObjectValue && clonedValue instanceof ObjectValue) {
    if (realm.react.reactProps.has(value)) {
      realm.react.reactProps.add(clonedValue);
    }
    if (value.isPartialObject()) {
      clonedValue.makePartial();
    }
    if (value.isSimpleObject()) {
      clonedValue.makeSimple("transitive");
    }
    if (value.mightBeFinalObject()) {
      clonedValue.makeFinal();
    }
  }
}

function deepCloneObjectPropertyDescriptor(
  realm: Realm,
  object: ObjectValue,
  clonedObject: ObjectValue,
  desc: PropertyDescriptor,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = deepCloneTemplateValue(realm, value, outlinedValue, runtimeValuesMap);
    clonedDesc.value = clonedValue;
  } else {
    invariant(false, "// TODO handle get/set in deepCloneObjectPropertyDescriptor");
  }
  return clonedDesc;
}

function deepCloneObjectProperties(
  realm: Realm,
  clonedObject: ObjectValue,
  val: ObjectValue,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
): void {
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
    let desc = deepCloneObjectPropertyDescriptor(realm, val, clonedObject, descriptor, outlinedValue, runtimeValuesMap);
    Properties.OrdinaryDefineOwnProperty(realm, clonedObject, propName, desc);
  }
  let unknownProperty = val.unknownProperty;
  if (unknownProperty !== undefined) {
    let desc;
    let key;
    if (unknownProperty.descriptor !== undefined) {
      desc = deepCloneObjectPropertyDescriptor(
        realm,
        val,
        clonedObject,
        unknownProperty.descriptor,
        outlinedValue,
        runtimeValuesMap
      );
    }
    if (unknownProperty.key !== undefined) {
      key = deepCloneTemplateValue(realm, unknownProperty.key, outlinedValue, runtimeValuesMap);
    }
    clonedObject.unknownProperty = {
      descriptor: desc,
      key,
      object: clonedObject,
    };
  }
  if (val.temporalAlias !== undefined) {
    clonedObject.temporalAlias = deepCloneTemplateValue(realm, val.temporalAlias, outlinedValue, runtimeValuesMap);
  }
}

function deepCloneArrayWithNumericWidenedProperty(
  realm: Realm,
  val: ArrayValue,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
): ArrayValue {
  let intrinsicName;
  if (isTemporalValueDeeplyReferencingKnownObject(realm, val)) {
    intrinsicName = getIntrinsicNameFromTemporalValueDeeplyReferencingPropsObject(realm, val);
    if (realm.react.outlinedTemporalValue.has(intrinsicName)) {
      let arrayLikeObject = realm.react.outlinedTemporalValue.get(intrinsicName);
      invariant(arrayLikeObject instanceof ArrayValue);
      return arrayLikeObject;
    }
  }
  let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
  invariant(temporalOperationEntry !== undefined);
  let { args, operationDescriptor } = temporalOperationEntry;
  let clonedArgs = args.map(arg => deepCloneTemplateValue(realm, arg, outlinedValue, runtimeValuesMap));
  if (operationDescriptor.type === "UNKNOWN_ARRAY_METHOD_PROPERTY_CALL") {
    let possibleNestedOptimizedFunctions;
    let [, methodProperty, callbackfn] = clonedArgs;
    invariant(methodProperty instanceof StringValue);
    // For now we only support nested optimized functions on map and filter
    if (methodProperty.value === "map" || methodProperty.value === "filter") {
      possibleNestedOptimizedFunctions = [
        {
          func: callbackfn,
          thisValue: realm.intrinsics.undefined,
          kind: methodProperty.value,
        },
      ];
    }
    let clonedArrayLikeObject = ArrayValue.createTemporalWithWidenedNumericProperty(
      realm,
      clonedArgs,
      createOperationDescriptor("UNKNOWN_ARRAY_METHOD_PROPERTY_CALL"),
      possibleNestedOptimizedFunctions
    );
    if (intrinsicName !== undefined) {
      realm.react.outlinedTemporalValue.set(intrinsicName, clonedArrayLikeObject);
    }
    return clonedArrayLikeObject;
  } else if (operationDescriptor.type === "UNKNOWN_ARRAY_METHOD_CALL") {
    let clonedArrayLikeObject = ArrayValue.createTemporalWithWidenedNumericProperty(
      realm,
      clonedArgs,
      createOperationDescriptor("UNKNOWN_ARRAY_METHOD_CALL")
    );
    if (intrinsicName !== undefined) {
      realm.react.outlinedTemporalValue.set(intrinsicName, clonedArrayLikeObject);
    }
    return clonedArrayLikeObject;
  }
  invariant(false, "TODO");
}

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

function deepCloneFunctionValueFunctionScopeForBindings(
  realm: Realm,
  scope: LexicalEnvironment,
  bindings: Set<string>,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
) {
  let env = new LexicalEnvironment(realm);
  let dclRec = new DeclarativeEnvironmentRecord(realm);
  dclRec.creatingOptimizedFunction = scope.environmentRecord.creatingOptimizedFunction;
  dclRec.lexicalEnvironment = env;
  env.environmentRecord = dclRec;
  if (bindings.size > 0) {
    for (let bindingName of bindings) {
      let binding = getBinding(bindingName, scope);
      // If the binding is null then it's in global scope so we don't need to clone
      if (binding !== null && binding.value !== undefined) {
        let clonedBinding = Object.assign({}, binding);
        clonedBinding.environment = dclRec;
        clonedBinding.value = deepCloneTemplateValue(realm, binding.value, outlinedValue, runtimeValuesMap);
        dclRec.bindings[bindingName] = clonedBinding;
      }
    }
  }
  env.parent = scope.parent;
  return env;
}

function deepCloneFunctionValue(
  realm: Realm,
  val: ECMAScriptSourceFunctionValue,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
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
  let clonedScope = deepCloneFunctionValueFunctionScopeForBindings(
    realm,
    val.$Environment,
    bindings,
    outlinedValue,
    runtimeValuesMap
  );
  let clonedFunction = Functions.FunctionCreate(realm, val.$FunctionKind, params, body, clonedScope, val.$Strict);
  return clonedFunction;
}

function deepCloneTemplateConcreteValue(
  realm: Realm,
  val: ConcreteValue,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
): Value {
  if (val instanceof PrimitiveValue || val instanceof NativeFunctionValue) {
    return val;
  }
  if (val.isPartialObject()) {
    invariant(false, "TODO");
  }
  if (val instanceof ArrayValue) {
    if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
      return deepCloneArrayWithNumericWidenedProperty(realm, val, outlinedValue, runtimeValuesMap);
    }
    invariant(val.$Prototype === realm.intrinsics.ArrayPrototype);
    let clonedObject = new ArrayValue(realm);
    // alreadyCloned.set(val, clonedObject);
    deepCloneObjectProperties(realm, clonedObject, val, outlinedValue, runtimeValuesMap);
    applyPostValueConfig(realm, val, clonedObject);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    if (val instanceof BoundFunctionValue) {
      invariant(false, "TODO");
    }
    invariant(val instanceof ECMAScriptSourceFunctionValue);
    return deepCloneFunctionValue(realm, val, outlinedValue, runtimeValuesMap);
  }
  invariant(val.$Prototype === realm.intrinsics.ObjectPrototype);
  let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  // alreadyCloned.set(val, clonedObject);
  deepCloneObjectProperties(realm, clonedObject, val, outlinedValue, runtimeValuesMap);
  applyPostValueConfig(realm, val, clonedObject);
  return clonedObject;
}

function deepCloneTemplateAbstractValue(
  realm: Realm,
  val: AbstractValue,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
): Value {
  const kind = val.kind;
  if (val.isTemporal()) {
    let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
    invariant(temporalOperationEntry !== undefined);
    let [originalFunction] = temporalOperationEntry.args;
    return originalFunction;
  } else if (kind === "conditional") {
    let [condValue, consequentVal, alternateVal] = val.args;

    let clonedCondValue = deepCloneTemplateValue(realm, condValue, outlinedValue, runtimeValuesMap);
    let clonedConsequentVal = deepCloneTemplateValue(realm, consequentVal, outlinedValue, runtimeValuesMap);
    let clonedAlternateVal = deepCloneTemplateValue(realm, alternateVal, outlinedValue, runtimeValuesMap);
    return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
  } else if (kind === "||" || kind === "&&") {
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = deepCloneTemplateValue(realm, leftValue, outlinedValue, runtimeValuesMap);
    let clonedRightValue = deepCloneTemplateValue(realm, rightValue, outlinedValue, runtimeValuesMap);
    return AbstractValue.createFromLogicalOp(realm, val.kind, clonedLeftValue, clonedRightValue);
  }
  debugger;
}

function deepCloneTemplateValue(
  realm: Realm,
  val: Value,
  outlinedValue: AbstractObjectValue,
  runtimeValuesMap: Map<Value, string>
): Value {
  if (runtimeValuesMap.has(val)) {
    if (val instanceof AbstractValue) {
      if (val.kind === "outlined function call") {
        let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
        invariant(temporalOperationEntry !== undefined);
        let [outlinedFunc, ...args] = temporalOperationEntry.args;
        if (realm.react.reactOutliningModels.has(outlinedFunc)) {
          let clonedArgs = args.map(arg => deepCloneTemplateValue(realm, arg, outlinedValue, runtimeValuesMap));
          return buildTemplateFromInnerFunctionCallModel(realm, outlinedFunc, clonedArgs);
        }
      } else if (val.kind === "stub function") {
        let temporalOperationEntry = realm.getTemporalOperationEntryFromDerivedValue(val);
        invariant(temporalOperationEntry !== undefined);
        let [originalFunction] = temporalOperationEntry.args;
        return originalFunction;
      }
    }
    let id = runtimeValuesMap.get(val);
    return Get(realm, outlinedValue, id + "");
  }
  if (val instanceof ConcreteValue) {
    return deepCloneTemplateConcreteValue(realm, val, outlinedValue, runtimeValuesMap);
  } else if (val instanceof AbstractValue) {
    return deepCloneTemplateAbstractValue(realm, val, outlinedValue, runtimeValuesMap);
  }
}

function getReactComponentModelInWidenedEnvironment(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  writeEffects: WriteEffects
): { effects: Effects, tempate: Value, runtimeValuesMap: Map<Value, number> } {
  let runtimeValuesMap = new Map();
  let template;

  let [effects] = getValueAndEffectsFromFunctionCall(realm, true, () => {
    // Model the props object as the first argument for this function
    let thisValue = realm.intrinsics.undefined; // We only deal with function components, so there is no "this"
    let args = [getInitialProps(realm, func, {})]; // We only support props (TODO: need to support forwardRef). No legacy context.
    // Temporarily create a new env for the function
    let originalEnv = func.$Environment;
    let widenedEnvForFunction = createWidenedEnvForFunctionComponent(realm, func, writeEffects);
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

    let reactRuntimeValues = Create.ArrayCreate(realm, runtimeValues.size);

    let index = 0;
    for (let runtimeValue of runtimeValues) {
      Properties.Set(realm, reactRuntimeValues, index + "", runtimeValue, true);
      runtimeValuesMap.set(runtimeValue, index);
      index++;
    }
    return reactRuntimeValues;
  });

  return { effects, template, runtimeValuesMap };
}

function getFunctionCallModelInWidenedEnvironment(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  writeEffects: WriteEffects
): { effects: Effects, tempate: Value, runtimeValuesMap: Map<Value, number> } | void {
  let runtimeValuesMap = new Map();
  let template;
  let skipTemplate = false;

  let [effects] = getValueAndEffectsFromFunctionCall(realm, true, () => {
    // Temporarily create a new env for the function
    let originalEnv = func.$Environment;
    let widenedEnvForFunction = createWidenedEnvForFunctionComponent(realm, func, writeEffects);
    func.$Environment = widenedEnvForFunction;
    try {
      let funcCall = Utils.createModelledFunctionCall(realm, func);
      template = realm.isInPureScope() ? funcCall() : realm.evaluateWithPureScope(funcCall);
    } catch (e) {
      debugger;
      throw new ReactModelingFailure(`Failed to evaluate function ${getName(realm, func)} due to an error.`);
    } finally {
      func.$Environment = originalEnv;
    }

    let runtimeValues = new Set();
    collectRuntimeValuesNeededForReactTemplateFromValue(realm, template, runtimeValues);
    if (runtimeValues.size === 0 || (runtimeValues.size === 1 && Array.from(runtimeValues)[0] === template)) {
      skipTemplate = true;
      return realm.intrinsics.undefined;
    }

    let reactRuntimeValues = Create.ArrayCreate(realm, runtimeValues.size);

    let index = 0;
    for (let runtimeValue of runtimeValues) {
      Properties.Set(realm, reactRuntimeValues, index + "", runtimeValue, true);
      runtimeValuesMap.set(runtimeValue, index);
      index++;
    }
    return reactRuntimeValues;
  });

  return !skipTemplate ? { effects, template, runtimeValuesMap } : undefined;
}

export function modelReactComponentTreeRoots(realm: Realm, func: FunctionValue, writeEffects: WriteEffects): void {
  invariant(func instanceof ECMAScriptSourceFunctionValue);
  if (realm.react.reactOutliningModels.has(func)) {
    return;
  }
  let model = getReactComponentModelInWidenedEnvironment(realm, func, writeEffects);
  realm.react.reactOutliningModels.set(func, { writeEffects, ...model });
}

function modelReactComponentInnerFunctionCall(realm: Realm, func: FunctionValue, writeEffects: WriteEffects): void {
  invariant(func instanceof ECMAScriptSourceFunctionValue);
  if (realm.react.reactOutliningModels.has(func)) {
    return;
  }
  let model = getFunctionCallModelInWidenedEnvironment(realm, func, writeEffects);
  if (model === undefined) {
    return;
  }
  let parentOptimizedFunction = realm.currentOptimizedFunction;
  realm.react.reactOutliningModels.set(func, model);
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

function shallowCloneFunctionValue(realm: Realm, func: ECMAScriptSourceFunctionValue): ECMAScriptSourceFunctionValue {
  if (realm.react.originalFuncToClonedFunc.has(func)) {
    let clonedFunc = realm.react.originalFuncToClonedFunc.get(func);
    invariant(clonedFunc instanceof ECMAScriptSourceFunctionValue);
    return clonedFunc;
  }
  let body = ((t.cloneDeep(t.blockStatement([func.$ECMAScriptCode])): any): BabelNodeBlockStatement);
  let params = func.$FormalParameters;
  invariant(func.isValid());
  let clonedFunc = Functions.FunctionCreate(realm, func.$FunctionKind, params, body, func.$Environment, func.$Strict);
  realm.react.shallowClonedRootComponents.add(clonedFunc);
  return clonedFunc;
}

function createOutlinedFunctionCall(
  realm: Realm,
  effects: Effects,
  funcVal: ECMAScriptSourceFunctionValue,
  args: Array<Value>
): AbstractObjectValue {
  let outlinedFuncCall = AbstractValue.createTemporalFromBuildFunction(
    realm,
    ObjectValue,
    [funcVal, ...args],
    createOperationDescriptor("REACT_TEMPORAL_FUNC"),
    { skipInvariant: true }
  );
  let outlinedFuncCallValues = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
  outlinedFuncCallValues.intrinsicName = outlinedFuncCall.intrinsicName;
  outlinedFuncCallValues.intrinsicNameGenerated = true;
  outlinedFuncCall.values = new ValuesDomain(new Set([outlinedFuncCallValues]));
  outlinedFuncCall.makePartial();
  outlinedFuncCall.makeSimple("transitive");
  return outlinedFuncCall;
}

function buildTemplateFromInnerFunctionCallModel(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  args: Array<Value>
): Value {
  let model = realm.react.reactOutliningModels.get(func);
  invariant(model !== undefined);
  let { effects, runtimeValuesMap, template, writeEffects } = model;
  let outlinedValue = createOutlinedFunctionCall(realm, effects, func, args, writeEffects);
  let clonedTemplate = getValueWithPreviousEffectsApplied(realm, effects, () =>
    deepCloneTemplateValue(realm, template, outlinedValue, runtimeValuesMap)
  );
  return clonedTemplate;
}

export function buildTemplateFromComponentModel(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue,
  args: Array<Value>,
  isRoot: true
): Value {
  let funcToUse = func;
  if (isRoot) {
    funcToUse = shallowCloneFunctionValue(realm, func);
  }
  let model = realm.react.reactOutliningModels.get(func);
  invariant(model !== undefined);
  let { effects, runtimeValuesMap, template, writeEffects } = model;
  let outlinedValue = createOutlinedFunctionCall(realm, effects, funcToUse, args, writeEffects);
  let clonedTemplate = getValueWithPreviousEffectsApplied(realm, effects, () =>
    deepCloneTemplateValue(realm, template, outlinedValue, runtimeValuesMap)
  );

  let parentOptimizedFunction = realm.currentOptimizedFunction;
  let modeledFunctionEffects = createAdditionalEffects(
    realm,
    effects,
    false,
    "ReactModeledFunctionEffects",
    funcToUse,
    parentOptimizedFunction
  );
  writeEffects.set(funcToUse, modeledFunctionEffects);
  return clonedTemplate;
}
