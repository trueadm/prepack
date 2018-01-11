/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { Realm, type Effects } from "../realm.js";
import {
  Value,
  AbstractValue,
  ArrayValue,
  ObjectValue,
  NumberValue,
  StringValue,
  ReactOpcodeValue,
  ECMAScriptSourceFunctionValue,
} from "../values/index.js";
import { Generator } from "../utils/generator.js";
import type { ReactBytecodeTree, ReactBytecodeComponent } from "../serializer/types.js";
import { Properties, Create } from "../singletons.js";
import { Get, IsArray } from "../methods/index.js";
import { isReactElement, forEachArrayValue } from "./utils.js";
import invariant from "../invariant.js";
import type { FunctionBodyAstNode } from "../types.js";
import * as t from "babel-types";

const ELEMENT_OPEN = { value: 1, hint: "ELEMENT_OPEN" };
const ELEMENT_OPEN_DIV = { value: 2, hint: "ELEMENT_OPEN_DIV" };
const ELEMENT_OPEN_SPAN = { value: 3, hint: "ELEMENT_OPEN_SPAN" };
const ELEMENT_CLOSE = { value: 4, hint: "ELEMENT_CLOSE" };

const CONDITIONAL = { value: 5, hint: "CONDITIONAL" };

const PROPERTY_STATIC_CLASS_NAME = { value: 20, hint: "PROPERTY_STATIC_CLASS_NAME" };

const TEXT_STATIC_CONTENT = { value: 26, hint: "TEXT_STATIC_CONTENT" };
const TEXT_STATIC_NODE = { value: 27, hint: "TEXT_STATIC_NODE" };

const UNKNOWN_CHILDREN = { value: 34, hint: "UNKNOWN_CHILDREN" };
const UNKNOWN_NODE = { value: 35, hint: "UNKNOWN_NODE" };

type BytecodeComponentState = {
  instructions: Array<Value>,
  slotIndex: number,
  valueCache: Map<Value, NumberValue>,
  values: Array<Value>,
};

function convertJSArrayToArrayValue(jsArray, realm): ArrayValue {
  let arrayValue = Create.ArrayCreate(realm, 0, realm.intrinsics.ArrayPrototype);

  for (let i = 0; i < jsArray.length; i++) {
    Create.CreateDataPropertyOrThrow(realm, arrayValue, "" + i, jsArray[i]);
  }
  Properties.Set(realm, arrayValue, "length", new NumberValue(realm, jsArray.length), false);
  return arrayValue;
}

function createOpcode(realm: Realm, code) {
  return new ReactOpcodeValue(realm, code.value, code.hint);
}

function createFunction(realm: Realm, formalParameters: Array<BabelNode>): ECMAScriptSourceFunctionValue {
  let func = new ECMAScriptSourceFunctionValue(realm);
  let body = t.blockStatement([]);
  func.$FormalParameters = formalParameters;
  func.$ECMAScriptCode = body;
  ((body: any): FunctionBodyAstNode).uniqueOrderedTag = realm.functionBodyUniqueTagSeed++;
  return func;
}

function getSlotIndexForValue(realm: Realm, value: Value, bytecodeComponentState: BytecodeComponentState) {
  let slotIndexForValue;

  if (bytecodeComponentState.valueCache.has(value)) {
    let cachedValue = bytecodeComponentState.valueCache.get(value);
    invariant(cachedValue instanceof NumberValue);
    slotIndexForValue = cachedValue;
  } else {
    slotIndexForValue = new NumberValue(realm, bytecodeComponentState.slotIndex++);
    bytecodeComponentState.valueCache.set(value, slotIndexForValue);
    bytecodeComponentState.values.push(value);
  }

  return slotIndexForValue;
}

function getSlotIndexForNode(realm: Realm, node: null | Value, bytecodeComponentState: BytecodeComponentState) {
  let slotIndexForNode;

  if (node === null) {
    slotIndexForNode = new NumberValue(realm, bytecodeComponentState.slotIndex++);
    bytecodeComponentState.values.push(realm.intrinsics.null);
  }
  invariant(slotIndexForNode instanceof NumberValue);

  return slotIndexForNode;
}

function createInstructionsFromAbstractValue(
  realm: Realm,
  abstractValue: AbstractValue,
  node: null | Value,
  bytecodeComponentState: BytecodeComponentState,
  isChild: boolean
): void {
  switch (abstractValue.kind) {
    case "conditional":
      // testValue is what gives us truthy/falsey
      let testValue = abstractValue.args[0];

      // handle sebsquent value first
      let subsequentValue = abstractValue.args[1];
      let subsequentBytecodeComponentState = {
        children: [],
        instructions: [],
        slotIndex: 0,
        valueCache: new Map(),
        values: [],
      };
      createInstructionsFromValue(realm, subsequentValue, subsequentBytecodeComponentState);
      const subsequentInstructions = convertJSArrayToArrayValue(subsequentBytecodeComponentState.instructions, realm);
      const subsequentSlots = convertJSArrayToArrayValue(subsequentBytecodeComponentState.values, realm);

      // handle alternative value second
      let alternativeValue = abstractValue.args[2];
      let alternativeBytecodeComponentState = {
        children: [],
        instructions: [],
        slotIndex: 0,
        valueCache: new Map(),
        values: [],
      };
      createInstructionsFromValue(realm, alternativeValue, alternativeBytecodeComponentState);
      const alternativeInstructions = convertJSArrayToArrayValue(alternativeBytecodeComponentState.instructions, realm);
      const alternativeSlots = convertJSArrayToArrayValue(alternativeBytecodeComponentState.values, realm);

      // put both values together in a conditional
      invariant(testValue instanceof AbstractValue);
      let conditionalValue = AbstractValue.createFromConditionalOp(realm, testValue, subsequentSlots, alternativeSlots);

      let slotIndexForTestValue = getSlotIndexForValue(realm, testValue, bytecodeComponentState);
      let slotIndexForBytecodeNode = getSlotIndexForNode(realm, null, bytecodeComponentState);
      let slotIndexForBranchSlots = getSlotIndexForValue(realm, conditionalValue, bytecodeComponentState);

      bytecodeComponentState.instructions.push(
        createOpcode(realm, CONDITIONAL),
        slotIndexForTestValue,
        slotIndexForBytecodeNode,
        slotIndexForBranchSlots,
        subsequentInstructions,
        alternativeInstructions
      );
      break;
    case "resolved":
    default:
      let slotIndexForValue = getSlotIndexForValue(realm, abstractValue, bytecodeComponentState);
      let slotIndexForNode = getSlotIndexForNode(realm, null, bytecodeComponentState);

      bytecodeComponentState.instructions.push(
        createOpcode(realm, isChild ? UNKNOWN_CHILDREN : UNKNOWN_NODE),
        slotIndexForValue,
        slotIndexForNode
      );
  }
}

function createInstructionsFromReactElementValue(
  realm: Realm,
  reactElement: ObjectValue,
  bytecodeComponentState: BytecodeComponentState
): void {
  let typeValue = Get(realm, reactElement, "type");
  let propsValue = Get(realm, reactElement, "props");

  invariant(propsValue instanceof ObjectValue);
  if (typeValue instanceof StringValue) {
    let stringValue = typeValue.value;
    if (stringValue === "div") {
      bytecodeComponentState.instructions.push(createOpcode(realm, ELEMENT_OPEN_DIV));
    } else if (stringValue === "span") {
      bytecodeComponentState.instructions.push(createOpcode(realm, ELEMENT_OPEN_SPAN));
    } else {
      bytecodeComponentState.instructions.push(createOpcode(realm, ELEMENT_OPEN), typeValue);
    }

    for (let [propName] of propsValue.properties) {
      let propValue = Get(realm, propsValue, propName);

      if (propName === "children") {
        if (propValue instanceof StringValue || propValue instanceof NumberValue) {
          bytecodeComponentState.instructions.push(createOpcode(realm, TEXT_STATIC_CONTENT), propValue);
        } else if (propValue instanceof AbstractValue) {
          createInstructionsFromAbstractValue(realm, propValue, reactElement, bytecodeComponentState, true);
        } else if (isReactElement(propValue)) {
          invariant(propValue instanceof ObjectValue);
          createInstructionsFromReactElementValue(realm, propValue, bytecodeComponentState);
        } else if (IsArray(realm, propValue)) {
          invariant(propValue instanceof ObjectValue);
          forEachArrayValue(realm, propValue, childValue => {
            createInstructionsFromValue(realm, childValue, bytecodeComponentState);
          });
        }
      } else if (propName === "className") {
        if (propValue instanceof StringValue) {
          bytecodeComponentState.instructions.push(createOpcode(realm, PROPERTY_STATIC_CLASS_NAME), propValue);
        }
      }
    }
    bytecodeComponentState.instructions.push(createOpcode(realm, ELEMENT_CLOSE));
  }
}

function createInstructionsFromValue(realm: Realm, value: Value, bytecodeComponentState: BytecodeComponentState): void {
  if (isReactElement(value)) {
    invariant(value instanceof ObjectValue);
    createInstructionsFromReactElementValue(realm, value, bytecodeComponentState);
  } else if (value instanceof StringValue || value instanceof NumberValue) {
    bytecodeComponentState.instructions.push(createOpcode(realm, TEXT_STATIC_NODE), value);
  } else if (value instanceof AbstractValue) {
    createInstructionsFromAbstractValue(realm, value, null, bytecodeComponentState, false);
  } else {
    // TODO
  }
}

export function withBytecodeComponentEffects(realm: Realm, effects: Effects, f: Function) {
  let [
    value,
    generator,
    modifiedBindings,
    modifiedProperties: Map<PropertyBinding, void | Descriptor>,
    createdObjects,
  ] = effects;
  realm.applyEffects([value, new Generator(realm), modifiedBindings, modifiedProperties, createdObjects]);
  let val = f(generator, value);
  realm.restoreBindings(modifiedBindings);
  realm.restoreProperties(modifiedProperties);
  return val;
}

export function createReactBytecodeComponent(realm: Realm, effects: Effects): ReactBytecodeComponent {
  return withBytecodeComponentEffects(realm, effects, (generator, value) => {
    let bytecodeComponentState = {
      children: [],
      instructions: [],
      slotIndex: 0,
      valueCache: new Map(),
      values: [],
    };
    let slotsFunc = createFunction(realm, [t.identifier("instance"), t.identifier("props")]);
    let instructionsFunc = createFunction(realm, []);
    let nodeValue = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);

    Create.CreateDataPropertyOrThrow(realm, nodeValue, "$i", instructionsFunc);
    Create.CreateDataPropertyOrThrow(realm, nodeValue, "$s", slotsFunc);
    Create.CreateDataPropertyOrThrow(realm, nodeValue, "_c", realm.intrinsics.null);

    createInstructionsFromValue(realm, value, bytecodeComponentState);

    return {
      children: bytecodeComponentState.children,
      effects,
      instructionsFunc,
      instructions: convertJSArrayToArrayValue(bytecodeComponentState.instructions, realm),
      nodeValue,
      slotsFunc,
      values: bytecodeComponentState.values,
    };
  });
}

export function createReactBytecodeTree(realm: Realm, effects: Effects): ReactBytecodeTree {
  let rootBytecodeComponent = createReactBytecodeComponent(realm, effects);

  return {
    rootBytecodeComponent,
  };
}
