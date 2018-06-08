/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { Realm, Effects } from "../realm.js";
import { ValuesDomain } from "../domains/index.js";
import { AbruptCompletion, PossiblyNormalCompletion } from "../completions.js";
import type { BabelNode, BabelNodeJSXIdentifier } from "babel-types";
import { parseExpression } from "babylon";
import {
  AbstractObjectValue,
  AbstractValue,
  ArrayValue,
  BooleanValue,
  BoundFunctionValue,
  ECMAScriptFunctionValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  NumberValue,
  ObjectValue,
  StringValue,
  SymbolValue,
  UndefinedValue,
  Value,
} from "../values/index.js";
import { Generator } from "../utils/generator.js";
import type {
  Descriptor,
  FunctionBodyAstNode,
  ReactComponentTreeConfig,
  ReactHint,
  PropertyBinding,
} from "../types.js";
import { Get, cloneDescriptor } from "../methods/index.js";
import { computeBinary } from "../evaluators/BinaryExpression.js";
import type { AdditionalFunctionEffects, ReactEvaluatedNode } from "../serializer/types.js";
import invariant from "../invariant.js";
import { Create, Properties, To } from "../singletons.js";
import traverse from "babel-traverse";
import * as t from "babel-types";
import type { BabelNodeStatement } from "babel-types";
import { CompilerDiagnostic, FatalError } from "../errors.js";

export type ReactSymbolTypes =
  | "react.element"
  | "react.context"
  | "react.provider"
  | "react.fragment"
  | "react.portal"
  | "react.return"
  | "react.call";

export function isReactElement(val: Value): boolean {
  if (!(val instanceof ObjectValue)) {
    return false;
  }
  let realm = val.$Realm;
  if (!realm.react.enabled) {
    return false;
  }
  if (realm.react.reactElements.has(val)) {
    return true;
  }
  if (!val.properties.has("type") || !val.properties.has("props") || !val.properties.has("$$typeof")) {
    return false;
  }
  let $$typeof = getProperty(realm, val, "$$typeof");
  let globalObject = realm.$GlobalObject;
  let globalSymbolValue = getProperty(realm, globalObject, "Symbol");

  if (globalSymbolValue === realm.intrinsics.undefined) {
    if ($$typeof instanceof NumberValue) {
      return $$typeof.value === 0xeac7;
    }
  } else if ($$typeof instanceof SymbolValue) {
    let symbolFromRegistry = realm.globalSymbolRegistry.find(e => e.$Symbol === $$typeof);
    let _isReactElement = symbolFromRegistry !== undefined && symbolFromRegistry.$Key === "react.element";
    if (_isReactElement) {
      // add to Set to speed up future lookups
      realm.react.reactElements.add(val);
      return true;
    }
  }
  return false;
}

export function getReactSymbol(symbolKey: ReactSymbolTypes, realm: Realm): SymbolValue {
  let reactSymbol = realm.react.symbols.get(symbolKey);
  if (reactSymbol !== undefined) {
    return reactSymbol;
  }
  let SymbolFor = realm.intrinsics.Symbol.properties.get("for");
  if (SymbolFor !== undefined) {
    let SymbolForDescriptor = SymbolFor.descriptor;

    if (SymbolForDescriptor !== undefined) {
      let SymbolForValue = SymbolForDescriptor.value;
      if (SymbolForValue instanceof ObjectValue && typeof SymbolForValue.$Call === "function") {
        reactSymbol = SymbolForValue.$Call(realm.intrinsics.Symbol, [new StringValue(realm, symbolKey)]);
        invariant(reactSymbol instanceof SymbolValue);
        realm.react.symbols.set(symbolKey, reactSymbol);
      }
    }
  }
  invariant(reactSymbol instanceof SymbolValue, `Symbol("${symbolKey}") could not be found in realm`);
  return reactSymbol;
}

export function isTagName(ast: BabelNode): boolean {
  return ast.type === "JSXIdentifier" && /^[a-z]|\-/.test(((ast: any): BabelNodeJSXIdentifier).name);
}

export function isReactComponent(name: string) {
  return name.length > 0 && name[0] === name[0].toUpperCase();
}

export function valueIsClassComponent(realm: Realm, value: Value): boolean {
  if (!(value instanceof FunctionValue)) {
    return false;
  }
  let prototype = Get(realm, value, "prototype");

  if (prototype instanceof ObjectValue) {
    return To.ToBooleanPartial(realm, Get(realm, prototype, "isReactComponent"));
  }
  return false;
}

export function valueIsKnownReactAbstraction(realm: Realm, value: Value): boolean {
  return value instanceof AbstractObjectValue && realm.react.abstractHints.has(value);
}

// logger isn't typed otherwise it will increase flow cycle length :()
export function valueIsReactLibraryObject(realm: Realm, value: ObjectValue, logger: any): boolean {
  if (realm.fbLibraries.react === value) {
    return true;
  }
  // we check that the object is the React or React-like library by checking for
  // core properties that should exist on it
  let reactVersion = logger.tryQuery(() => Get(realm, value, "version"), undefined);
  if (!(reactVersion instanceof StringValue)) {
    return false;
  }
  let reactCreateElement = logger.tryQuery(() => Get(realm, value, "createElement"), undefined);
  if (!(reactCreateElement instanceof FunctionValue)) {
    return false;
  }
  let reactCloneElement = logger.tryQuery(() => Get(realm, value, "cloneElement"), undefined);
  if (!(reactCloneElement instanceof FunctionValue)) {
    return false;
  }
  let reactIsValidElement = logger.tryQuery(() => Get(realm, value, "isValidElement"), undefined);
  if (!(reactIsValidElement instanceof FunctionValue)) {
    return false;
  }
  let reactComponent = logger.tryQuery(() => Get(realm, value, "Component"), undefined);
  if (!(reactComponent instanceof FunctionValue)) {
    return false;
  }
  let reactChildren = logger.tryQuery(() => Get(realm, value, "Children"), undefined);
  if (!(reactChildren instanceof ObjectValue)) {
    return false;
  }
  return false;
}

export function valueIsLegacyCreateClassComponent(realm: Realm, value: Value): boolean {
  if (!(value instanceof FunctionValue)) {
    return false;
  }
  let prototype = Get(realm, value, "prototype");

  if (prototype instanceof ObjectValue) {
    return prototype.properties.has("__reactAutoBindPairs");
  }
  return false;
}

export function valueIsFactoryClassComponent(realm: Realm, value: Value): boolean {
  if (value instanceof ObjectValue) {
    return To.ToBooleanPartial(realm, Get(realm, value, "render"));
  }
  return false;
}

export function addKeyToReactElement(realm: Realm, reactElement: ObjectValue): ObjectValue {
  let typeValue = getProperty(realm, reactElement, "type");
  let refValue = getProperty(realm, reactElement, "ref");
  let propsValue = getProperty(realm, reactElement, "props");
  // we need to apply a key when we're branched
  let currentKeyValue = getProperty(realm, reactElement, "key") || realm.intrinsics.null;
  let uniqueKey = getUniqueReactElementKey("", realm.react.usedReactElementKeys);
  let newKeyValue = new StringValue(realm, uniqueKey);
  if (currentKeyValue !== realm.intrinsics.null) {
    newKeyValue = computeBinary(realm, "+", currentKeyValue, newKeyValue);
  }
  invariant(propsValue instanceof ObjectValue || propsValue instanceof AbstractObjectValue);
  return createInternalReactElement(realm, typeValue, newKeyValue, refValue, propsValue);
}
// we create a unique key for each JSXElement to prevent collisions
// otherwise React will detect a missing/conflicting key at runtime and
// this can break the reconcilation of JSXElements in arrays
export function getUniqueReactElementKey(index?: string, usedReactElementKeys: Set<string>) {
  let key;
  do {
    key = Math.random()
      .toString(36)
      .replace(/[^a-z]+/g, "")
      .substring(0, 2);
  } while (usedReactElementKeys.has(key));
  usedReactElementKeys.add(key);
  if (index !== undefined) {
    return `${key}${index}`;
  }
  return key;
}

// a helper function to loop over ArrayValues
export function forEachArrayValue(
  realm: Realm,
  array: ArrayValue,
  mapFunc: (element: Value, index: number) => void
): void {
  let lengthValue = Get(realm, array, "length");
  invariant(lengthValue instanceof NumberValue, "TODO: support non-numeric length on forEachArrayValue");
  let length = lengthValue.value;
  for (let i = 0; i < length; i++) {
    let elementProperty = array.properties.get("" + i);
    let elementPropertyDescriptor = elementProperty && elementProperty.descriptor;
    if (elementPropertyDescriptor) {
      let elementValue = elementPropertyDescriptor.value;
      if (elementValue instanceof Value) {
        mapFunc(elementValue, i);
      }
    }
  }
}

export function mapArrayValue(
  realm: Realm,
  array: ArrayValue,
  mapFunc: (element: Value, descriptor: Descriptor) => Value
): ArrayValue {
  let lengthValue = Get(realm, array, "length");
  invariant(lengthValue instanceof NumberValue, "TODO: support non-numeric length on mapArrayValue");
  let length = lengthValue.value;
  let newArray = Create.ArrayCreate(realm, length);
  let returnTheNewArray = false;

  for (let i = 0; i < length; i++) {
    let elementProperty = array.properties.get("" + i);
    let elementPropertyDescriptor = elementProperty && elementProperty.descriptor;
    if (elementPropertyDescriptor) {
      let elementValue = elementPropertyDescriptor.value;
      if (elementValue instanceof Value) {
        let newElement = mapFunc(elementValue, elementPropertyDescriptor);
        if (newElement !== elementValue) {
          returnTheNewArray = true;
        }
        Create.CreateDataPropertyOrThrow(realm, newArray, "" + i, newElement);
        continue;
      }
    }
    Create.CreateDataPropertyOrThrow(realm, newArray, "" + i, realm.intrinsics.undefined);
  }
  return returnTheNewArray ? newArray : array;
}

function GetDescriptorForProperty(value: ObjectValue, propertyName: string): ?Descriptor {
  let object = value.properties.get(propertyName);
  invariant(object);
  return object.descriptor;
}

export function convertSimpleClassComponentToFunctionalComponent(
  realm: Realm,
  complexComponentType: ECMAScriptSourceFunctionValue,
  additionalFunctionEffects: AdditionalFunctionEffects
): void {
  let prototype = complexComponentType.properties.get("prototype");
  invariant(prototype);
  invariant(prototype.descriptor);
  prototype.descriptor.configurable = true;
  Properties.DeletePropertyOrThrow(realm, complexComponentType, "prototype");

  // change the function kind
  complexComponentType.$FunctionKind = "normal";
  // set the prototype back to an object
  complexComponentType.$Prototype = realm.intrinsics.FunctionPrototype;
  // give the function the functional components params
  complexComponentType.$FormalParameters = [t.identifier("props"), t.identifier("context")];
  // add a transform to occur after the additional function has serialized the body of the class
  additionalFunctionEffects.transforms.push((body: Array<BabelNodeStatement>) => {
    // as this was a class before and is now a functional component, we need to replace
    // this.props and this.context to props and context, via the function arugments
    let funcNode = t.functionExpression(null, [], t.blockStatement(body));

    traverse(
      t.file(t.program([t.expressionStatement(funcNode)])),
      {
        "Identifier|ThisExpression"(path) {
          let node = path.node;
          if ((t.isIdentifier(node) && node.name === "this") || t.isThisExpression(node)) {
            let parentPath = path.parentPath;
            let parentNode = parentPath.node;

            if (t.isMemberExpression(parentNode)) {
              // remove the "this" from the member
              parentPath.replaceWith(parentNode.property);
            } else {
              throw new FatalError(
                `conversion of a simple class component to functional component failed due to "this" not being replaced`
              );
            }
          }
        },
      },
      undefined,
      {},
      undefined
    );
    traverse.clearCache();
  });
}

function createBinding(descriptor: void | Descriptor, key: string | SymbolValue, object: ObjectValue) {
  return {
    descriptor,
    key,
    object,
  };
}

function cloneProperties(realm: Realm, properties: Map<string, any>, object: ObjectValue): Map<string, any> {
  let newProperties = new Map();
  for (let [propertyName, { descriptor }] of properties) {
    newProperties.set(propertyName, createBinding(cloneDescriptor(descriptor), propertyName, object));
  }
  return newProperties;
}

function cloneSymbols(realm: Realm, symbols: Map<SymbolValue, any>, object: ObjectValue): Map<SymbolValue, any> {
  let newSymbols = new Map();
  for (let [symbol, { descriptor }] of symbols) {
    newSymbols.set(symbol, createBinding(cloneDescriptor(descriptor), symbol, object));
  }
  return newSymbols;
}

function cloneValue(
  realm: Realm,
  originalValue: Value,
  _prototype: null | ObjectValue,
  copyToObject?: ObjectValue
): Value {
  if (originalValue instanceof FunctionValue) {
    return cloneFunction(realm, originalValue, _prototype, copyToObject);
  }
  invariant(false, "TODO: add support to cloneValue() for more value types");
}

function cloneFunction(
  realm: Realm,
  originalValue: Value,
  _prototype: null | ObjectValue,
  copyToObject?: ObjectValue
): FunctionValue {
  let newValue;
  if (originalValue instanceof ECMAScriptSourceFunctionValue) {
    newValue = copyToObject || new ECMAScriptSourceFunctionValue(realm, originalValue.intrinsicName);
    invariant(newValue instanceof ECMAScriptSourceFunctionValue);
    // $FlowFixMe: complains about Object.assign
    Object.assign(newValue, originalValue);
    let properties = cloneProperties(realm, originalValue.properties, newValue);
    newValue.properties = properties;
    let symbols = cloneSymbols(realm, originalValue.symbols, newValue);
    newValue.symbols = symbols;

    // handle home object + prototype
    let originalPrototype = originalValue.$HomeObject;
    invariant(originalPrototype instanceof ObjectValue);
    let prototype = _prototype || clonePrototype(realm, originalPrototype);
    newValue.$HomeObject = prototype;
    if (originalPrototype.properties.has("constructor")) {
      Properties.Set(realm, prototype, "constructor", newValue, false);
    }
    if (originalValue.properties.has("prototype")) {
      Properties.Set(realm, newValue, "prototype", prototype, false);
    }
  }
  invariant(newValue instanceof FunctionValue, "TODO: add support to cloneValue() for more function types");
  return newValue;
}

function clonePrototype(realm: Realm, prototype: Value): ObjectValue {
  invariant(prototype instanceof ObjectValue);
  let newPrototype = new ObjectValue(realm, realm.intrinsics.ObjectPrototype, prototype.intrinsicName);

  Object.assign(newPrototype, prototype);
  for (let [propertyName] of prototype.properties) {
    if (propertyName !== "constructor") {
      let originalValue = Get(realm, prototype, propertyName);
      let newValue = cloneValue(realm, originalValue, prototype);
      Properties.Set(realm, newPrototype, propertyName, newValue, false);
    }
  }
  for (let [symbol] of prototype.symbols) {
    let originalValue = Get(realm, prototype, symbol);
    let newValue = cloneValue(realm, originalValue, prototype);
    Properties.Set(realm, newPrototype, symbol, newValue, false);
  }
  return newPrototype;
}

const skipFunctionProperties = new Set(["length", "prototype", "arguments", "name", "caller"]);

export function convertFunctionalComponentToComplexClassComponent(
  realm: Realm,
  functionalComponentType: ECMAScriptSourceFunctionValue,
  complexComponentType: void | ECMAScriptSourceFunctionValue,
  additionalFunctionEffects: AdditionalFunctionEffects
): void {
  invariant(complexComponentType instanceof ECMAScriptSourceFunctionValue);
  // get all properties on the functional component that were added in user-code
  // we add defaultProps as undefined, as merging a class component's defaultProps on to
  // a differnet component isn't right, we can discard defaultProps instead via folding
  // we also don't want propTypes from the class component, so we remove that too
  let userCodePropertiesToAdd: Map<string, PropertyBinding> = new Map([
    ["defaultProps", createBinding(undefined, "defaultProps", functionalComponentType)],
    ["propTypes", createBinding(undefined, "propTypes", functionalComponentType)],
  ]);
  let userCodeSymbolsToAdd: Map<SymbolValue, PropertyBinding> = new Map();

  for (let [propertyName, binding] of functionalComponentType.properties) {
    if (!skipFunctionProperties.has(propertyName)) {
      userCodePropertiesToAdd.set(propertyName, binding);
    }
  }
  for (let [symbol, binding] of functionalComponentType.symbols) {
    userCodeSymbolsToAdd.set(symbol, binding);
  }

  cloneValue(realm, complexComponentType, null, functionalComponentType);
  // then copy back and properties that were on the original functional component
  // ensuring we overwrite any existing ones
  for (let [propertyName, binding] of userCodePropertiesToAdd) {
    functionalComponentType.properties.set(propertyName, binding);
  }
  for (let [symbol, binding] of userCodeSymbolsToAdd) {
    functionalComponentType.symbols.set(symbol, binding);
  }
  // add a transform to occur after the additional function has serialized the body of the class
  additionalFunctionEffects.transforms.push((body: Array<BabelNodeStatement>) => {
    // as we've converted a functional component to a complex one, we are going to have issues with
    // "props" and "context" references, as they're now going to be "this.props" and "this.context".
    // we simply need a to add to vars to beginning of the body to get around this
    // if they're not used, any DCE tool post-Prepack (GCC or Uglify) will remove them
    body.unshift(
      t.variableDeclaration("var", [
        t.variableDeclarator(t.identifier("props"), t.memberExpression(t.thisExpression(), t.identifier("props"))),
        t.variableDeclarator(t.identifier("context"), t.memberExpression(t.thisExpression(), t.identifier("context"))),
      ])
    );
  });
}

export function normalizeFunctionalComponentParamaters(func: ECMAScriptSourceFunctionValue): void {
  // fix the length as we may change the arguments
  let lengthProperty = GetDescriptorForProperty(func, "length");
  invariant(lengthProperty);
  lengthProperty.writable = false;
  lengthProperty.enumerable = false;
  lengthProperty.configurable = true;
  func.$FormalParameters = func.$FormalParameters.map((param, i) => {
    if (i === 0) {
      return t.isIdentifier(param) ? param : t.identifier("props");
    } else {
      return t.isIdentifier(param) ? param : t.identifier("context");
    }
  });
  if (func.$FormalParameters.length === 1) {
    func.$FormalParameters.push(t.identifier("context"));
  }
  // ensure the length value is set to the correct value after
  // we've made mutations to the arguments of this function
  let lengthValue = lengthProperty.value;
  invariant(lengthValue instanceof NumberValue);
  lengthValue.value = func.$FormalParameters.length;
}

export function createReactHintObject(
  object: ObjectValue,
  propertyName: string,
  args: Array<Value>,
  firstRenderValue: Value
): ReactHint {
  return {
    firstRenderValue,
    object,
    propertyName,
    args,
  };
}

export function getComponentTypeFromRootValue(realm: Realm, value: Value): ECMAScriptSourceFunctionValue | null {
  let _valueIsKnownReactAbstraction = valueIsKnownReactAbstraction(realm, value);
  if (!(value instanceof ECMAScriptSourceFunctionValue || _valueIsKnownReactAbstraction)) {
    return null;
  }
  if (_valueIsKnownReactAbstraction) {
    invariant(value instanceof AbstractValue);
    let reactHint = realm.react.abstractHints.get(value);

    invariant(reactHint);
    if (typeof reactHint !== "string" && reactHint.object === realm.fbLibraries.reactRelay) {
      switch (reactHint.propertyName) {
        case "createFragmentContainer":
        case "createPaginationContainer":
        case "createRefetchContainer":
          invariant(Array.isArray(reactHint.args));
          // componentType is the 1st argument of a ReactRelay container
          let componentType = reactHint.args[0];
          invariant(componentType instanceof ECMAScriptSourceFunctionValue);
          return componentType;
        default:
          invariant(
            false,
            `unsupported known React abstraction - ReactRelay property "${reactHint.propertyName}" not supported`
          );
      }
    }
    if (reactHint.object === realm.fbLibraries.react && reactHint.propertyName === "forwardRef") {
      return null;
    }
    invariant(false, "unsupported known React abstraction");
  } else {
    invariant(value instanceof ECMAScriptSourceFunctionValue);
    return value;
  }
}

export function flagPropsWithNoPartialKeyOrRef(realm: Realm, props: ObjectValue | AbstractObjectValue): void {
  realm.react.propsWithNoPartialKeyOrRef.add(props);
}

export function hasNoPartialKeyOrRef(realm: Realm, props: ObjectValue | AbstractObjectValue): boolean {
  if (realm.react.propsWithNoPartialKeyOrRef.has(props)) {
    return true;
  }
  if (props instanceof ObjectValue && !props.isPartialObject()) {
    return true;
  }
  if (props instanceof AbstractObjectValue) {
    if (props.values.isTop()) {
      return false;
    }
    let elements = props.values.getElements();
    if (elements.size === 1) {
      props = Array.from(elements)[0];
    } else {
      for (let element of elements) {
        let wasSafe = hasNoPartialKeyOrRef(realm, element);
        if (!wasSafe) {
          return false;
        }
      }
      return true;
    }
  }
  if (props instanceof ObjectValue && props.properties.has("key") && props.properties.has("ref")) {
    return true;
  }
  return false;
}

function recursivelyFlattenArray(realm: Realm, array, targetArray): void {
  forEachArrayValue(realm, array, item => {
    if (item instanceof ArrayValue && !item.intrinsicName) {
      recursivelyFlattenArray(realm, item, targetArray);
    } else {
      let lengthValue = Get(realm, targetArray, "length");
      invariant(lengthValue instanceof NumberValue);
      Properties.Set(realm, targetArray, "" + lengthValue.value, item, true);
    }
  });
}

export function flattenChildren(realm: Realm, array: ArrayValue): ArrayValue {
  let flattenedChildren = Create.ArrayCreate(realm, 0);
  recursivelyFlattenArray(realm, array, flattenedChildren);
  return flattenedChildren;
}

export function evaluateWithNestedParentEffects(realm: Realm, nestedEffects: Array<Effects>, f: () => Effects) {
  let nextEffects = nestedEffects.slice();
  let modifiedBindings;
  let modifiedProperties;
  let createdObjects;
  let value;

  if (nextEffects.length !== 0) {
    let effects = nextEffects.shift();
    value = effects.result;
    createdObjects = effects.createdObjects;
    modifiedBindings = effects.modifiedBindings;
    modifiedProperties = effects.modifiedProperties;
    realm.applyEffects(
      new Effects(
        value,
        new Generator(realm, "evaluateWithNestedEffects"),
        modifiedBindings,
        modifiedProperties,
        createdObjects
      )
    );
  }
  try {
    if (nextEffects.length === 0) {
      return f();
    } else {
      return evaluateWithNestedParentEffects(realm, nextEffects, f);
    }
  } finally {
    if (modifiedBindings && modifiedProperties) {
      realm.undoBindings(modifiedBindings);
      realm.restoreProperties(modifiedProperties);
    }
  }
}

// This function is mainly use to get internal properties
// on objects that we know are safe to access internally
// such as ReactElements. Getting properties here does
// not emit change to modified bindings and is intended
// for only internal usage – not for user-land code
export function getProperty(
  realm: Realm,
  object: ObjectValue | AbstractObjectValue,
  property: string | SymbolValue
): Value {
  if (object instanceof AbstractObjectValue) {
    if (object.values.isTop()) {
      return realm.intrinsics.undefined;
    }
    let elements = object.values.getElements();
    invariant(elements);
    if (elements.size > 0) {
      object = Array.from(elements)[0];
    } else {
      // intentionally left in
      invariant(false, "TODO: should we hit this?");
    }
    invariant(object instanceof ObjectValue);
  }
  let binding;
  if (typeof property === "string") {
    binding = object.properties.get(property);
  } else {
    binding = object.symbols.get(property);
  }
  if (!binding) {
    return realm.intrinsics.undefined;
  }
  let descriptor = binding.descriptor;

  if (!descriptor) {
    return realm.intrinsics.undefined;
  }
  let value = descriptor.value;
  if (value === undefined) {
    AbstractValue.reportIntrospectionError(object, `react/utils/getProperty unsupported getter/setter property`);
    throw new FatalError();
  }
  invariant(value instanceof Value, `react/utils/getProperty should not be called on internal properties`);
  return value;
}

export function createReactEvaluatedNode(
  status:
    | "ROOT"
    | "NEW_TREE"
    | "INLINED"
    | "BAIL-OUT"
    | "FATAL"
    | "UNKNOWN_TYPE"
    | "RENDER_PROPS"
    | "FORWARD_REF"
    | "NORMAL",
  name: string
): ReactEvaluatedNode {
  return {
    children: [],
    message: "",
    name,
    status,
  };
}

export function getComponentName(realm: Realm, componentType: Value): string {
  if (componentType instanceof SymbolValue && componentType === getReactSymbol("react.fragment", realm)) {
    return "React.Fragment";
  } else if (componentType instanceof SymbolValue) {
    return "unknown symbol";
  }
  // $FlowFixMe: this code is fine, Flow thinks that coponentType is bound to string...
  if (isReactComponent(componentType)) {
    return "ReactElement";
  }
  if (componentType === realm.intrinsics.undefined || componentType === realm.intrinsics.null) {
    return "no name";
  }
  invariant(
    componentType instanceof ECMAScriptSourceFunctionValue ||
      componentType instanceof BoundFunctionValue ||
      componentType instanceof AbstractObjectValue ||
      componentType instanceof AbstractValue ||
      componentType instanceof ObjectValue
  );
  let boundText = componentType instanceof BoundFunctionValue ? "bound " : "";

  if (componentType.__originalName) {
    return boundText + componentType.__originalName;
  }
  if (realm.fbLibraries.reactRelay !== undefined) {
    if (componentType === Get(realm, realm.fbLibraries.reactRelay, "QueryRenderer")) {
      return boundText + "QueryRenderer";
    }
  }
  if (componentType instanceof ECMAScriptSourceFunctionValue && componentType.$Prototype !== undefined) {
    let name = Get(realm, componentType, "name");

    if (name instanceof StringValue) {
      return boundText + name.value;
    }
  }
  if (realm.react.abstractHints.has(componentType)) {
    let reactHint = realm.react.abstractHints.get(componentType);

    invariant(reactHint !== undefined);
    if (reactHint.object === realm.fbLibraries.react && reactHint.propertyName === "forwardRef") {
      return "forwarded ref";
    }
  }
  if (componentType instanceof FunctionValue) {
    return boundText + "anonymous";
  }
  return "unknown";
}

export function convertConfigObjectToReactComponentTreeConfig(
  realm: Realm,
  config: ObjectValue | UndefinedValue
): ReactComponentTreeConfig {
  // defaults
  let firstRenderOnly = false;

  if (!(config instanceof UndefinedValue)) {
    for (let [key] of config.properties) {
      let propValue = getProperty(realm, config, key);
      if (propValue instanceof StringValue || propValue instanceof NumberValue || propValue instanceof BooleanValue) {
        let value = propValue.value;

        // boolean options
        if (typeof value === "boolean") {
          if (key === "firstRenderOnly") {
            firstRenderOnly = value;
          }
        }
      } else {
        let diagnostic = new CompilerDiagnostic(
          "__optimizeReactComponentTree(rootComponent, config) has been called with invalid arguments",
          realm.currentLocation,
          "PP0024",
          "FatalError"
        );
        realm.handleError(diagnostic);
        if (realm.handleError(diagnostic) === "Fail") throw new FatalError();
      }
    }
  }
  return {
    firstRenderOnly,
  };
}

export function getValueFromFunctionCall(
  realm: Realm,
  func: ECMAScriptSourceFunctionValue | BoundFunctionValue,
  funcThis: ObjectValue | AbstractObjectValue | UndefinedValue,
  args: Array<Value>,
  isConstructor?: boolean = false
): Value {
  invariant(func.$Call, "Expected function to be a FunctionValue with $Call method");
  let funcCall = func.$Call;
  let newCall = func.$Construct;
  let completion;
  try {
    if (isConstructor) {
      invariant(newCall);
      completion = newCall(args, func);
    } else {
      completion = funcCall(funcThis, args);
    }
  } catch (error) {
    if (error instanceof AbruptCompletion) {
      completion = error;
    } else {
      throw error;
    }
  }
  if (completion instanceof PossiblyNormalCompletion) {
    // in this case one of the branches may complete abruptly, which means that
    // not all control flow branches join into one flow at this point.
    // Consequently we have to continue tracking changes until the point where
    // all the branches come together into one.
    completion = realm.composeWithSavedCompletion(completion);
  }
  // return or throw completion
  if (completion instanceof AbruptCompletion) throw completion;
  invariant(completion instanceof Value);
  return completion;
}

function isEventProp(name: string): boolean {
  return name.length > 2 && name[0].toLowerCase() === "o" && name[1].toLowerCase() === "n";
}

export function sanitizeReactElementForFirstRenderOnly(realm: Realm, reactElement: ObjectValue): ObjectValue {
  let typeValue = getProperty(realm, reactElement, "type");
  let keyValue = getProperty(realm, reactElement, "key");
  let propsValue = getProperty(realm, reactElement, "props");

  invariant(propsValue instanceof ObjectValue);
  return createInternalReactElement(
    realm,
    typeValue,
    keyValue,
    realm.intrinsics.null,
    typeValue instanceof StringValue ? cloneProps(realm, propsValue, true) : propsValue
  );
}

export function getLocationFromValue(expressionLocation: any) {
  // if we can't get a value, then it's likely that the source file was not given
  // (this happens in React tests) so instead don't print any location
  return expressionLocation
    ? ` at location: ${expressionLocation.start.line}:${expressionLocation.start.column} ` +
        `- ${expressionLocation.end.line}:${expressionLocation.end.line}`
    : "";
}

export function createNoopFunction(realm: Realm): ECMAScriptSourceFunctionValue {
  if (realm.react.noopFunction !== undefined) {
    return realm.react.noopFunction;
  }
  let noOpFunc = new ECMAScriptSourceFunctionValue(realm);
  let body = t.blockStatement([]);
  ((body: any): FunctionBodyAstNode).uniqueOrderedTag = realm.functionBodyUniqueTagSeed++;
  noOpFunc.$FormalParameters = [];
  noOpFunc.$ECMAScriptCode = body;
  realm.react.noopFunction = noOpFunc;
  return noOpFunc;
}

export function doNotOptimizeComponent(realm: Realm, componentType: Value): boolean {
  if (componentType instanceof ObjectValue) {
    let doNotOptimize = Get(realm, componentType, "__reactCompilerDoNotOptimize");

    if (doNotOptimize instanceof BooleanValue) {
      return doNotOptimize.value;
    }
  }
  return false;
}

export function createDefaultPropsHelper(realm: Realm): ECMAScriptSourceFunctionValue {
  let defaultPropsHelper = `
    function defaultPropsHelper(props, defaultProps) {
      for (var propName in defaultProps) {
        if (props[propName] === undefined) {
          props[propName] = defaultProps[propName];
        }
      }
      return props;
    }
  `;

  let escapeHelperAst = parseExpression(defaultPropsHelper, { plugins: ["flow"] });
  let helper = new ECMAScriptSourceFunctionValue(realm);
  let body = escapeHelperAst.body;
  ((body: any): FunctionBodyAstNode).uniqueOrderedTag = realm.functionBodyUniqueTagSeed++;
  helper.$ECMAScriptCode = body;
  helper.$FormalParameters = escapeHelperAst.params;
  return helper;
}

export function createInternalReactElement(
  realm: Realm,
  type: Value,
  key: Value,
  ref: Value,
  props: ObjectValue | AbstractObjectValue
): ObjectValue {
  let obj = Create.ObjectCreate(realm, realm.intrinsics.ObjectPrototype);

  // sanity checks
  if (type instanceof AbstractValue && type.kind === "conditional") {
    invariant(false, "createInternalReactElement should never encounter a conditional type");
  }
  if (props instanceof AbstractObjectValue && props.kind === "conditional") {
    invariant(false, "createInternalReactElement should never encounter a conditional props");
  }
  Create.CreateDataPropertyOrThrow(realm, obj, "$$typeof", getReactSymbol("react.element", realm));
  Create.CreateDataPropertyOrThrow(realm, obj, "type", type);
  Create.CreateDataPropertyOrThrow(realm, obj, "key", key);
  Create.CreateDataPropertyOrThrow(realm, obj, "ref", ref);
  Create.CreateDataPropertyOrThrow(realm, obj, "props", props);
  Create.CreateDataPropertyOrThrow(realm, obj, "_owner", realm.intrinsics.null);
  obj.makeFinal();
  return obj;
}

export function cloneProps(
  realm: Realm,
  props: ObjectValue,
  excludeEventProps: boolean,
  newChildren?: Value
): ObjectValue {
  let clonedProps = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);

  for (let [propName, binding] of props.properties) {
    if (binding && binding.descriptor && binding.descriptor.enumerable) {
      if (newChildren !== undefined && propName === "children") {
        Properties.Set(realm, clonedProps, propName, newChildren, true);
      } else if (!excludeEventProps || !isEventProp(propName)) {
        Properties.Set(realm, clonedProps, propName, getProperty(realm, props, propName), true);
      }
    }
  }

  if (props.isPartialObject()) {
    clonedProps.makePartial();
  }
  if (props.isSimpleObject()) {
    clonedProps.makeSimple();
  }
  if (realm.react.propsWithNoPartialKeyOrRef.has(props)) {
    flagPropsWithNoPartialKeyOrRef(realm, clonedProps);
  }
  if (props.temporalAlias !== undefined) {
    clonedProps.temporalAlias = props.temporalAlias;
  }
  clonedProps.makeFinal();
  return clonedProps;
}

export function applyObjectAssignConfigsForReactElement(realm: Realm, to: ObjectValue, sources: Array<Value>): void {
  // get the global Object.assign
  let globalObj = Get(realm, realm.$GlobalObject, "Object");
  invariant(globalObj instanceof ObjectValue);
  let objAssign = Get(realm, globalObj, "assign");
  invariant(objAssign instanceof ECMAScriptFunctionValue);
  let objectAssignCall = objAssign.$Call;
  invariant(objectAssignCall !== undefined);

  const tryToApplyObjectAssign = () => {
    let effects;
    let savedSuppressDiagnostics = realm.suppressDiagnostics;
    try {
      realm.suppressDiagnostics = true;
      effects = realm.evaluateForEffects(
        () => objectAssignCall(realm.intrinsics.undefined, [to, ...sources]),
        undefined,
        "tryToApplyObjectAssign"
      );
    } catch (error) {
      if (error instanceof FatalError) {
        // if the built-in Object.assign failed, we need to recover
        realm.suppressDiagnostics = savedSuppressDiagnostics;
        let delayedSources = [];

        for (let obj of sources) {
          // ignore null or undefined
          if (obj === realm.intrinsics.null || obj === realm.intrinsics.undefined) {
            continue;
          }
          let source = To.ToObject(realm, obj);
          // the object is simple and partial so we can safely copy over properties
          if (source instanceof ObjectValue && !source.isPartialObject()) {
            for (let [propName, binding] of source.properties) {
              if (binding.descriptor !== undefined) {
                Properties.Set(realm, to, propName, Get(realm, source, propName), true);
              }
            }
            delayedSources.push(source.getSnapshot());
          } else {
            // if we are dealing with an abstract object or one that is partial, then
            // we don't try and copy its properties over as there's no guarantee they are
            // safe to copy
            if (source instanceof AbstractObjectValue && source.kind === "explicit conversion to object") {
              // Make it implicit again since it is getting delayed into an Object.assign call.
              delayedSources.push(source.args[0]);
            } else {
              delayedSources.push(source.getSnapshot());
            }
            // if to has properties, we better remove them because after the temporal call to Object.assign we don't know their values anymore
            if (to.hasStringOrSymbolProperties()) {
              // preserve them in a snapshot and add the snapshot to the sources
              delayedSources.push(to.getSnapshot({ removeProperties: true }));
            }
          }
        }
        // prepare our temporal Object.assign fallback
        to.makePartial();
        to.makeSimple();
        let temporalTo = AbstractValue.createTemporalFromBuildFunction(
          realm,
          ObjectValue,
          [objAssign, to, ...delayedSources],
          ([methodNode, ..._args]) => {
            return t.callExpression(methodNode, ((_args: any): Array<any>));
          },
          { skipInvariant: true }
        );
        invariant(temporalTo instanceof AbstractObjectValue);
        temporalTo.values = new ValuesDomain(to);
        to.temporalAlias = temporalTo;
        return;
      } else {
        throw error;
      }
    } finally {
      realm.suppressDiagnostics = savedSuppressDiagnostics;
    }
    // Note that the effects of (non joining) abrupt branches are not included
    // in effects, but are tracked separately inside completion.
    realm.applyEffects(effects);
    let completion = effects.result;
    if (completion instanceof PossiblyNormalCompletion) {
      // in this case one of the branches may complete abruptly, which means that
      // not all control flow branches join into one flow at this point.
      // Consequently we have to continue tracking changes until the point where
      // all the branches come together into one.
      completion = realm.composeWithSavedCompletion(completion);
    }
    // return or throw completion
    if (completion instanceof AbruptCompletion) throw completion;
  };

  if (realm.isInPureScope()) {
    tryToApplyObjectAssign();
  } else {
    objectAssignCall(realm.intrinsics.undefined, [to, ...sources]);
  }
}
