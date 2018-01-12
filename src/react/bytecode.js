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
  ReactSlotPointerValue,
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

// const FRAGMENT_OPEN = { value: 5, hint: "FRAGMENT_OPEN" };
// const FRAGMENT_CLOSE = { value: 6, hint: "FRAGMENT_CLOSE" };

const CONDITIONAL = { value: 7, hint: "CONDITIONAL" };

const PROPERTY_STATIC_CLASS_NAME = { value: 20, hint: "PROPERTY_STATIC_CLASS_NAME" };
const PROPERTY_DYNAMIC_CLASS_NAME = { value: 23, hint: "PROPERTY_DYNAMIC_CLASS_NAME" };

const TEXT_STATIC_CONTENT = { value: 26, hint: "TEXT_STATIC_CONTENT" };
const TEXT_DYNAMIC_CONTENT = { value: 27, hint: "TEXT_DYNAMIC_CONTENT" };
const TEXT_STATIC_NODE = { value: 28, hint: "TEXT_STATIC_NODE" };
const TEXT_DYNAMIC_NODE = { value: 29, hint: "TEXT_DYNAMIC_NODE" };

const UNKNOWN_CHILDREN = { value: 34, hint: "UNKNOWN_CHILDREN" };
const UNKNOWN_NODE = { value: 35, hint: "UNKNOWN_NODE" };

type BytecodeComponentState = {
  instructions: Array<Value>,
  isBranch: boolean,
  slotIndex: number,
  valueCache: Map<Value, NumberValue>,
  nodeCache: Map<Value, NumberValue>,
  values: Array<Value>,
};

type ConditionalShortCircuit = {
  status: "NONE" | "EQUAL" | "PARTIALLY_EQUAL",
  instructions?: Array<Value | Array<Value>>,
};

function convertJSArrayToArrayValue(jsArray, realm): ArrayValue {
  let arrayValue = Create.ArrayCreate(realm, 0, realm.intrinsics.ArrayPrototype);

  for (let i = 0; i < jsArray.length; i++) {
    Create.CreateDataPropertyOrThrow(realm, arrayValue, "" + i, jsArray[i]);
  }
  Properties.Set(realm, arrayValue, "length", new NumberValue(realm, jsArray.length), false);
  return arrayValue;
}

function changeOpcode(realm: Realm, opcodeValue: ReactOpcodeValue, newCode): ReactOpcodeValue {
  opcodeValue.value = newCode.value;
  opcodeValue.hint = newCode.hint;
  return opcodeValue;
}

function createOpcode(realm: Realm, code): ReactOpcodeValue {
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

function getSlotIndexForValue(
  realm: Realm,
  value: Value,
  bytecodeComponentState: BytecodeComponentState
): ReactSlotPointerValue {
  let slotIndexForValue;

  if (bytecodeComponentState.valueCache.has(value)) {
    let cachedValue = bytecodeComponentState.valueCache.get(value);
    invariant(cachedValue instanceof ReactSlotPointerValue);
    slotIndexForValue = cachedValue;
  } else {
    slotIndexForValue = new ReactSlotPointerValue(realm, bytecodeComponentState.slotIndex++);
    bytecodeComponentState.valueCache.set(value, slotIndexForValue);
    bytecodeComponentState.values.push(value);
  }
  return slotIndexForValue;
}

function getSlotIndexForNode(
  realm: Realm,
  node: null | Value,
  bytecodeComponentState: BytecodeComponentState
): ReactSlotPointerValue {
  let slotIndexForNode;

  if (node === null) {
    slotIndexForNode = new ReactSlotPointerValue(realm, bytecodeComponentState.slotIndex++);
    bytecodeComponentState.values.push(realm.intrinsics.null);
  } else if (bytecodeComponentState.nodeCache.has(node)) {
    let cachedValue = bytecodeComponentState.nodeCache.get(node);
    invariant(cachedValue instanceof ReactSlotPointerValue);
    slotIndexForNode = cachedValue;
  } else {
    slotIndexForNode = new ReactSlotPointerValue(realm, bytecodeComponentState.slotIndex++);
    bytecodeComponentState.nodeCache.set(node, slotIndexForNode);
    bytecodeComponentState.values.push(realm.intrinsics.null);
  }
  invariant(slotIndexForNode instanceof ReactSlotPointerValue);

  return slotIndexForNode;
}

function adjustInstructionSlotPointer(
  value: ReactSlotPointerValue,
  bytecodeComponentState: BytecodeComponentState
): Value {
  let offset = bytecodeComponentState.slotIndex;
  value.value += offset;
  bytecodeComponentState.slotIndex = value.value + 1;
  return value;
}

function adjustInstructionSlotPointers(
  instructions: Array<Value>,
  bytecodeComponentState: BytecodeComponentState
): Array<Value> {
  let offset = bytecodeComponentState.slotIndex;
  let lastOffset = offset;

  for (let i = 0; i < instructions.length; i++) {
    let item = instructions[i];

    if (item instanceof ReactSlotPointerValue) {
      item.value += offset;
      lastOffset = item.value;
    }
  }
  bytecodeComponentState.slotIndex = lastOffset + 1;
  return instructions;
}

function diffConditionalInstructions(
  a: Array<Value>,
  b: Array<Value>,
  alternativeBytecodeComponentState: BytecodeComponentState
): ConditionalShortCircuit {
  let lastItemWastStatic = false;
  let instructionsArePartiallyEqual = false;
  let instructions = [];
  let maxLength = a.length > b.length ? b.length : a.length;

  for (let i = 0; i < maxLength; i++) {
    let aItem = a[i];
    let bItem = b[i];

    if (aItem instanceof ReactOpcodeValue && bItem instanceof ReactOpcodeValue) {
      // if opcodes match
      if (aItem.value === bItem.value) {
        instructions.push(aItem);
        if (aItem.value === TEXT_STATIC_CONTENT.value || aItem.value === TEXT_STATIC_NODE.value) {
          lastItemWastStatic = true;
          continue;
        }
      } else {
        // there are some cases we can return partially equal when opcodes don't match
        // for example if they are both the same type but one is dynamic and the other is static
        // we can upgrade the static one to the dynamic one and then match them
        if (
          (aItem.value === TEXT_STATIC_NODE.value && bItem.value === TEXT_DYNAMIC_NODE.value) ||
          (aItem.value === TEXT_STATIC_CONTENT.value && bItem.value === TEXT_DYNAMIC_CONTENT.value)
        ) {
          lastItemWastStatic = true;
          instructionsArePartiallyEqual = true;
          instructions.push(bItem);
          // now we need to populate the next two instructions
          let staticValue = a[i + 1];
          let dynamicSlotPointerValue = b[i + 1];
          invariant(dynamicSlotPointerValue instanceof ReactSlotPointerValue);

          let dynamicValue = alternativeBytecodeComponentState.values[dynamicSlotPointerValue.value];
          invariant(dynamicValue instanceof Value);
          // we also need to push the static value into the next instruction
          instructions.push([staticValue, dynamicValue]);
          // then we skip over the entire dynamic text instruction
          i += 2;
          continue;
        }
        return { status: "NONE" };
      }
    } else if (aItem instanceof NumberValue && bItem instanceof NumberValue && aItem.value !== bItem.value) {
      if (!lastItemWastStatic) {
        return { status: "NONE" };
      } else {
        instructions.push([aItem, bItem]);
        instructionsArePartiallyEqual = true;
      }
    } else if (aItem instanceof StringValue && bItem instanceof StringValue && aItem.value !== bItem.value) {
      if (!lastItemWastStatic) {
        return { status: "NONE" };
      } else {
        instructions.push([aItem, bItem]);
        instructionsArePartiallyEqual = true;
      }
    }
    lastItemWastStatic = false;
  }
  return instructionsArePartiallyEqual ? { status: "PARTIALLY_EQUAL", instructions } : { status: "EQUAL" };
}

function createInstructionsFromAbstractValue(
  realm: Realm,
  abstractValue: AbstractValue,
  node: null | Value,
  bytecodeComponentState: BytecodeComponentState,
  opcodeValue: ReactOpcodeValue
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
        isBranch: true,
        slotIndex: 0,
        valueCache: new Map(),
        nodeCache: new Map(),
        values: [],
      };
      createInstructionsFromValue(realm, subsequentValue, subsequentBytecodeComponentState);
      // handle alternative value second
      let alternativeValue = abstractValue.args[2];
      let alternativeBytecodeComponentState = {
        children: [],
        instructions: [],
        isBranch: true,
        slotIndex: 0,
        valueCache: new Map(),
        nodeCache: new Map(),
        values: [],
      };
      createInstructionsFromValue(realm, alternativeValue, alternativeBytecodeComponentState);

      // check to see if we can short-circuit a conditonal statement to save bytecode size/CPU cycles
      let conditionalShortCircuit = diffConditionalInstructions(
        subsequentBytecodeComponentState.instructions,
        alternativeBytecodeComponentState.instructions,
        alternativeBytecodeComponentState
      );

      if (conditionalShortCircuit.status === "EQUAL") {
        if (!bytecodeComponentState.isBranch) {
          // ensure the first code is always the main opcode if we're not in a branch
          invariant(subsequentBytecodeComponentState.instructions.length > 0);
          subsequentBytecodeComponentState.instructions[0] = opcodeValue;
        }
        // add the instructions
        bytecodeComponentState.instructions.push(
          ...adjustInstructionSlotPointers(subsequentBytecodeComponentState.instructions, bytecodeComponentState)
        );
        // add the values
        bytecodeComponentState.values.push(...subsequentBytecodeComponentState.values);
      } else if (conditionalShortCircuit.status === "PARTIALLY_EQUAL") {
        let { instructions } = conditionalShortCircuit;
        invariant(instructions);
        let lastInstruction = null;

        for (let i = 0; i < instructions.length; i++) {
          let instruction = instructions[i];

          if (instruction instanceof ReactOpcodeValue) {
            bytecodeComponentState.instructions.push(instruction);
          } else if (instruction instanceof ReactSlotPointerValue) {
            bytecodeComponentState.instructions.push(adjustInstructionSlotPointer(instruction, bytecodeComponentState));
          } else if (Array.isArray(instruction)) {
            let [a, b] = instruction;

            // put together all values in a conditional
            // invariant(testValue instanceof AbstractValue);
            invariant(testValue instanceof AbstractValue);
            invariant(a instanceof Value);
            let conditionalValue = AbstractValue.createFromConditionalOp(realm, testValue, a, b);
            let slotIndexForConditionalValue = getSlotIndexForValue(realm, conditionalValue, bytecodeComponentState);
            let slotIndexForNode = getSlotIndexForNode(realm, node ? node : null, bytecodeComponentState);

            bytecodeComponentState.instructions.push(slotIndexForConditionalValue, slotIndexForNode);

            // we also need to upgrade the lastInstruction if it was a static one, to the dynamic equivilant
            if (lastInstruction instanceof ReactOpcodeValue) {
              switch (lastInstruction.value) {
                case TEXT_STATIC_NODE.value:
                  changeOpcode(realm, lastInstruction, node ? TEXT_DYNAMIC_CONTENT : TEXT_DYNAMIC_NODE);
                  break;
                case TEXT_STATIC_CONTENT.value:
                  changeOpcode(realm, lastInstruction, TEXT_DYNAMIC_CONTENT);
                  break;
                default:
              }
            }
          } else {
            bytecodeComponentState.instructions.push(instruction);
          }
          lastInstruction = instruction;
        }
      } else if (conditionalShortCircuit.status === "NONE") {
        // otherwise we continue to process the instructions in a condition
        const subsequentInstructions = convertJSArrayToArrayValue(subsequentBytecodeComponentState.instructions, realm);
        let subsequentSlots;
        // if the slots are empty, replace with null to avoid unnecessary array allocation
        if (subsequentBytecodeComponentState.values.length === 0) {
          subsequentSlots = realm.intrinsics.null;
        } else {
          subsequentSlots = convertJSArrayToArrayValue(subsequentBytecodeComponentState.values, realm);
        }
        const alternativeInstructions = convertJSArrayToArrayValue(
          alternativeBytecodeComponentState.instructions,
          realm
        );
        let alternativeSlots;
        // if the slots are empty, replace with null to avoid unnecessary array allocation
        if (alternativeBytecodeComponentState.values.length === 0) {
          alternativeSlots = realm.intrinsics.null;
        } else {
          alternativeSlots = convertJSArrayToArrayValue(alternativeBytecodeComponentState.values, realm);
        }

        // put both values together in a conditional
        invariant(testValue instanceof AbstractValue);
        let conditionalValue = AbstractValue.createFromConditionalOp(
          realm,
          testValue,
          subsequentSlots,
          alternativeSlots
        );

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
      }
      break;
    case "resolved":
    default:
      let slotIndexForValue = getSlotIndexForValue(realm, abstractValue, bytecodeComponentState);
      let slotIndexForNode = getSlotIndexForNode(realm, null, bytecodeComponentState);

      bytecodeComponentState.instructions.push(opcodeValue, slotIndexForValue, slotIndexForNode);
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
          createInstructionsFromAbstractValue(
            realm,
            propValue,
            reactElement,
            bytecodeComponentState,
            createOpcode(realm, UNKNOWN_CHILDREN)
          );
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
        } else if (propValue instanceof AbstractValue) {
          createInstructionsFromAbstractValue(
            realm,
            propValue,
            reactElement,
            bytecodeComponentState,
            createOpcode(realm, PROPERTY_DYNAMIC_CLASS_NAME)
          );
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
    createInstructionsFromAbstractValue(realm, value, null, bytecodeComponentState, createOpcode(realm, UNKNOWN_NODE));
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
      isBranch: false,
      slotIndex: 0,
      valueCache: new Map(),
      nodeCache: new Map(),
      values: [],
    };
    let slotsFunc = createFunction(realm, [t.identifier("instance"), t.identifier("props")]);
    let instructionsFunc = createFunction(realm, []);
    let nodeValue = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);

    // we use a, b, c properties to ensure minimum size
    Create.CreateDataPropertyOrThrow(realm, nodeValue, "a", instructionsFunc);
    Create.CreateDataPropertyOrThrow(realm, nodeValue, "b", slotsFunc);
    Create.CreateDataPropertyOrThrow(realm, nodeValue, "c", realm.intrinsics.null);

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
