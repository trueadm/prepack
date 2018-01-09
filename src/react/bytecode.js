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
import type { ReactBytecodeNode, ReactBytecodeValueNode } from "../serializer/types.js";
import { Properties, Create } from "../singletons.js";
import { Get } from "../methods/index.js";
import { isReactElement } from "./utils.js";
import invariant from "../invariant.js";
import { Generator } from "../utils/generator";
import type { FunctionBodyAstNode } from "../types.js";
import * as t from "babel-types";

const ELEMENT_OPEN = { value: 1, hint: "ELEMENT_OPEN" };
const ELEMENT_OPEN_DIV = { value: 2, hint: "ELEMENT_OPEN_DIV" };
const ELEMENT_OPEN_SPAN = { value: 3, hint: "ELEMENT_OPEN_SPAN" };
const ELEMENT_CLOSE = { value: 4, hint: "ELEMENT_CLOSE" };

// const FRAGMENT_OPEN = 5;
// const FRAGMENT_CLOSE = 6;

// const TERNARY = 7;
// const TERNARY_FROM_SLOT = 8;
// const REF_CALLBACK = 9;
// const LOOP_MAP = 10;
// const LOOP_MAP_FROM_SLOT = 11;
// const STORE_SLOT_VALUE = 12;

// const COMPONENT_INSTANCE = 13;
// const COMPONENT_LIFECYCLE_SHOULD_UPDATE = 14;
// const COMPONENT_LIFECYCLE_WILL_MOUNT = 15;
// const COMPONENT_LIFECYCLE_WILL_UPDATE = 16;
// const COMPONENT_LIFECYCLE_WILL_RECEIVE_PROPS = 17;
// const COMPONENT_LIFECYCLE_WILL_UNMOUNT = 18;
// const COMPONENT_LIFECYCLE_DID_MOUNT = 19;
// const COMPONENT_LIFECYCLE_DID_UPDATE = 20;
// const COMPONENT_LIFECYCLE_DID_CATCH = 21;

const PROPERTY_STATIC_CLASS_NAME = { value: 22, hint: "PROPERTY_STATIC_CLASS_NAME" };
// const PROPERTY_STATIC_ID = 23;
// const PROPERTY_STATIC_STYLE_CSS = 24;
// const PROPERTY_DYNAMIC_CLASS_NAME = 25;
// const PROPERTY_DYNAMIC_CLASS_NAME_FROM_SLOT = 26;
// const PROPERTY_DYNAMIC_ID = 27;
// const PROPERTY_DYNAMIC_ID_FROM_SLOT = 28;
// const PROPERTY_DYNAMIC_STYLE_CSS = 29;
// const PROPERTY_DYNAMIC_STYLE_CSS_FROM_SLOT = 30;

const TEXT_STATIC_CONTENT = { value: 31, hint: "TEXT_STATIC_CONTENT" };
// const TEXT_DYNAMIC_CONTENT = { value: 32, hint: "TEXT_DYNAMIC_CONTENT" };
const TEXT_STATIC_NODE = { value: 33, hint: "TEXT_STATIC_NODE" };
// const TEXT_DYNAMIC_NODE = { value: 34, hint: "TEXT_DYNAMIC_NODE" };
// const TEXT_DYNAMIC_NODE_FROM_SLOT = { value: 35, hint: "TEXT_DYNAMIC_NODE_FROM_SLOT" };

const UNKNOWN_CHILDREN = { value: 36, hint: "UNKNOWN_CHILDREN" };

// const ATTRIBUTE_STATIC = 37;
// const ATTRIBUTE_DYNAMIC = 38;
// const ATTRIBUTE_DYNAMIC_FROM_SLOT = 39;

// const EVENT_STATIC_BOUND = 40;
// const EVENT_DYNAMIC_BOUND = 41;
// const EVENT_DYNAMIC_BOUND_FROM_SLOT = 42;

type BytecodeNodeState = {
  instructions: Array<Value>,
  values: Map<Value, ReactBytecodeValueNode>,
  funcs: Set<ECMAScriptSourceFunctionValue>,
  slotIndex: number,
};

function convertJSArrayToArrayValue(jsArray, realm): ArrayValue {
  const arrayValue = Create.ArrayCreate(realm, 0, realm.intrinsics.ArrayPrototype);

  for (let i = 0; i < jsArray.length; i++) {
    Create.CreateDataPropertyOrThrow(realm, arrayValue, "" + i, jsArray[i]);
  }
  Properties.Set(realm, arrayValue, "length", new NumberValue(realm, jsArray.length), false);
  return arrayValue;
}

function createOpcode(realm: Realm, code) {
  return new ReactOpcodeValue(realm, code.value, code.hint);
}

function getBytecodeValueNode(
  realm: Realm,
  propValue: Value,
  bytecodeNodeState: BytecodeNodeState
): ReactBytecodeValueNode {
  if (bytecodeNodeState.values.has(propValue)) {
    let bytecodeNodeValueNode = bytecodeNodeState.values.get(propValue);
    invariant(bytecodeNodeValueNode);
    return bytecodeNodeValueNode;
  }
  let generator = realm.generator;
  invariant(generator instanceof Generator);

  let func = new ECMAScriptSourceFunctionValue(realm);
  let body = t.blockStatement([]);
  func.$FormalParameters = [];
  func.$ECMAScriptCode = body;
  ((body: any): FunctionBodyAstNode).uniqueOrderedTag = realm.functionBodyUniqueTagSeed++;

  let bytecodeValueNode = {
    func,
    generator,
    slotIndex: new NumberValue(realm, bytecodeNodeState.slotIndex++),
  };
  bytecodeNodeState.values.set(propValue, bytecodeValueNode);
  bytecodeNodeState.funcs.add(func);
  return bytecodeValueNode;
}

function createInstructionsFromReactElementValue(
  realm: Realm,
  reactElement: ObjectValue,
  bytecodeNodeState: BytecodeNodeState
): void {
  let typeValue = Get(realm, reactElement, "type");
  let propsValue = Get(realm, reactElement, "props");

  invariant(propsValue instanceof ObjectValue);
  if (typeValue instanceof StringValue) {
    let stringValue = typeValue.value;
    if (stringValue === "div") {
      bytecodeNodeState.instructions.push(createOpcode(realm, ELEMENT_OPEN_DIV));
    } else if (stringValue === "span") {
      bytecodeNodeState.instructions.push(createOpcode(realm, ELEMENT_OPEN_SPAN));
    } else {
      bytecodeNodeState.instructions.push(createOpcode(realm, ELEMENT_OPEN), typeValue);
    }

    for (let [propName] of propsValue.properties) {
      let propValue = Get(realm, propsValue, propName);

      if (propName === "children") {
        if (propValue instanceof StringValue) {
          bytecodeNodeState.instructions.push(createOpcode(realm, TEXT_STATIC_CONTENT), propValue);
        } else if (propValue instanceof AbstractValue) {
          let { func, slotIndex } = getBytecodeValueNode(realm, propValue, bytecodeNodeState);
          bytecodeNodeState.instructions.push(createOpcode(realm, UNKNOWN_CHILDREN), func, slotIndex);
        } else if (isReactElement(propValue)) {
          invariant(propValue instanceof ObjectValue);
          createInstructionsFromReactElementValue(realm, propValue, bytecodeNodeState);
        }
      } else if (propName === "className") {
        if (propValue instanceof StringValue) {
          bytecodeNodeState.instructions.push(createOpcode(realm, PROPERTY_STATIC_CLASS_NAME), propValue);
        }
      }
    }
    bytecodeNodeState.instructions.push(createOpcode(realm, ELEMENT_CLOSE));
  }
}

function createInstructionsFromValue(realm: Realm, value: Value, bytecodeNodeState: BytecodeNodeState): void {
  if (isReactElement(value)) {
    invariant(value instanceof ObjectValue);
    createInstructionsFromReactElementValue(realm, value, bytecodeNodeState);
  } else if (value instanceof StringValue || value instanceof NumberValue) {
    bytecodeNodeState.instructions.push(createOpcode(realm, TEXT_STATIC_NODE), value);
  } else {
    // TODO
  }
}

export function createReactBytecodeNode(realm: Realm, value: Value): ReactBytecodeNode {
  let bytecodeNodeState = {
    funcs: new Set(),
    instructions: [],
    slotIndex: 0,
    values: new Map(),
  };

  createInstructionsFromValue(realm, value, bytecodeNodeState);

  return {
    effects: null,
    funcs: bytecodeNodeState.funcs,
    instructions: convertJSArrayToArrayValue(bytecodeNodeState.instructions, realm),
    values: bytecodeNodeState.values,
  };
}
