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
import { Get, IsArray } from "../methods/index.js";
import { isReactElement, forEachArrayValue } from "./utils.js";
import invariant from "../invariant.js";
import { Generator } from "../utils/generator";
import type { FunctionBodyAstNode } from "../types.js";
import * as t from "babel-types";

const ELEMENT_OPEN = { value: 1, hint: "ELEMENT_OPEN" };
const ELEMENT_OPEN_DIV = { value: 2, hint: "ELEMENT_OPEN_DIV" };
const ELEMENT_OPEN_SPAN = { value: 3, hint: "ELEMENT_OPEN_SPAN" };
const ELEMENT_CLOSE = { value: 4, hint: "ELEMENT_CLOSE" };

const PROPERTY_STATIC_CLASS_NAME = { value: 20, hint: "PROPERTY_STATIC_CLASS_NAME" };

const TEXT_STATIC_CONTENT = { value: 26, hint: "TEXT_STATIC_CONTENT" };
const TEXT_STATIC_NODE = { value: 27, hint: "TEXT_STATIC_NODE" };

const UNKNOWN_CHILDREN = { value: 34, hint: "UNKNOWN_CHILDREN" };
// const UNKNOWN_NODE = { value: 35, hint: "UNKNOWN_NODE" };

type BytecodeNodeState = {
  funcs: Set<ECMAScriptSourceFunctionValue>,
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

function getBytecodeValueNode(
  realm: Realm,
  value: Value,
  subject: Value | null,
  bytecodeNodeState: BytecodeNodeState
): ReactBytecodeValueNode {
  let slotIndexForNode;
  let slotIndexForValue;

  if (bytecodeNodeState.valueCache.has(value)) {
    let cachedValue = bytecodeNodeState.valueCache.get(value);
    invariant(cachedValue instanceof NumberValue);
    slotIndexForValue = cachedValue;
  } else {
    slotIndexForValue = new NumberValue(realm, bytecodeNodeState.slotIndex++);
    bytecodeNodeState.valueCache.set(value, slotIndexForValue);
    bytecodeNodeState.values.push(value);
  }
  if (subject === null) {
    slotIndexForNode = new NumberValue(realm, bytecodeNodeState.slotIndex++);
    bytecodeNodeState.values.push(realm.intrinsics.null);
  }

  invariant(slotIndexForNode instanceof NumberValue);
  let bytecodeValueNode = {
    slotIndexForValue,
    slotIndexForNode,
  };
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
        if (propValue instanceof StringValue || propValue instanceof NumberValue) {
          bytecodeNodeState.instructions.push(createOpcode(realm, TEXT_STATIC_CONTENT), propValue);
        } else if (propValue instanceof AbstractValue) {
          let { slotIndexForValue, slotIndexForNode } = getBytecodeValueNode(realm, propValue, null, bytecodeNodeState);
          bytecodeNodeState.instructions.push(
            createOpcode(realm, UNKNOWN_CHILDREN),
            slotIndexForValue,
            slotIndexForNode
          );
        } else if (isReactElement(propValue)) {
          invariant(propValue instanceof ObjectValue);
          createInstructionsFromReactElementValue(realm, propValue, bytecodeNodeState);
        } else if (IsArray(realm, propValue)) {
          invariant(propValue instanceof ObjectValue);
          forEachArrayValue(realm, propValue, childValue => {
            createInstructionsFromValue(realm, childValue, bytecodeNodeState);
          });
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
  } else if (value instanceof AbstractValue) {
    let { slotIndexForValue, slotIndexForNode } = getBytecodeValueNode(realm, value, null, bytecodeNodeState);
    bytecodeNodeState.instructions.push(createOpcode(realm, UNKNOWN_CHILDREN), slotIndexForValue, slotIndexForNode);
  } else {
    // TODO
  }
}

export function createReactBytecodeNode(realm: Realm, value: Value): ReactBytecodeNode {
  let bytecodeNodeState = {
    funcs: new Set(),
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

  createInstructionsFromValue(realm, value, bytecodeNodeState);

  let generator = realm.generator;
  invariant(generator instanceof Generator);

  return {
    effects: null,
    funcs: bytecodeNodeState.funcs,
    generator,
    instructionsFunc,
    instructions: convertJSArrayToArrayValue(bytecodeNodeState.instructions, realm),
    nodeValue,
    slotsFunc,
    values: bytecodeNodeState.values,
  };
}
