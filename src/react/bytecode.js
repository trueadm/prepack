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
import { Value, AbstractValue, ArrayValue, ObjectValue, NumberValue, StringValue, ReactOpcodeValue } from "../values/index.js";
import { Properties, Create } from "../singletons.js";
import { Get } from "../methods/index.js";
import { isReactElement } from "./utils.js";
import invariant from "../invariant.js";

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

// const ATTRIBUTE_STATIC = 36;
// const ATTRIBUTE_DYNAMIC = 37;
// const ATTRIBUTE_DYNAMIC_FROM_SLOT = 38;

// const EVENT_STATIC_BOUND = 39;
// const EVENT_DYNAMIC_BOUND = 40;
// const EVENT_DYNAMIC_BOUND_FROM_SLOT = 41;

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

function createInstructionsFromReactElementValue(
  realm: Realm,
  reactElement: ObjectValue,
  instructions: Array<Value>
): void {
  let typeValue = Get(realm, reactElement, "type");
  let propsValue = Get(realm, reactElement, "props");

  invariant(propsValue instanceof ObjectValue);
  if (typeValue instanceof StringValue) {
    let stringValue = typeValue.value;
    if (stringValue === "div") {
      instructions.push(createOpcode(realm, ELEMENT_OPEN_DIV));
    } else if (stringValue === "span") {
      instructions.push(createOpcode(realm, ELEMENT_OPEN_SPAN));
    } else {
      instructions.push(createOpcode(realm, ELEMENT_OPEN), typeValue);
    }

    for (let [propName] of propsValue.properties) {
      const propValue = Get(realm, propsValue, propName);

      if (propName === "children") {
        if (propValue instanceof StringValue) {
          instructions.push(createOpcode(realm, TEXT_STATIC_CONTENT), propValue);
        } else if (propValue instanceof AbstractValue) {
          debugger;
        } else if (isReactElement(propValue)) {
          invariant(propValue instanceof ObjectValue);
          createInstructionsFromReactElementValue(realm, propValue, instructions);
        }
      } else if (propName === "className") {
        if (propValue instanceof StringValue) {
          instructions.push(createOpcode(realm, PROPERTY_STATIC_CLASS_NAME), propValue);
        }
      }
    }
    instructions.push(createOpcode(realm, ELEMENT_CLOSE));
  }
}

function createInstructionsFromValue(realm: Realm, value: Value, instructions: Array<Value>): void {
  if (isReactElement(value)) {
    invariant(value instanceof ObjectValue);
    createInstructionsFromReactElementValue(realm, value, instructions);
  } else if (value instanceof StringValue || value instanceof NumberValue) {
    instructions.push(createOpcode(realm, TEXT_STATIC_NODE), value);
  } else {
    // TODO
  }
}

export function createMountInstructions(realm: Realm, value: Value): ArrayValue {
  const mountInstructions = [];

  createInstructionsFromValue(realm, value, mountInstructions);

  return convertJSArrayToArrayValue(mountInstructions, realm);
}
