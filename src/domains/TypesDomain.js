/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import invariant from "../invariant.js";
import type { BabelBinaryOperator, BabelNodeLogicalOperator, BabelUnaryOperator } from "babel-types";
import {
  AbstractValue,
  BooleanValue,
  ConcreteValue,
  FunctionValue,
  NumberValue,
  ObjectValue,
  PrimitiveValue,
  StringValue,
  UndefinedValue,
  Value,
} from "../values/index.js";

/* An abstract domain for the type of value a variable might have.  */

export default class TypesDomain {
  constructor(type: void | typeof Value) {
    invariant(type !== ConcreteValue, "Concrete values must be specific");
    this._type = type === Value ? undefined : type;
  }

  static topVal: TypesDomain = new TypesDomain(undefined);

  _type: void | typeof Value;

  getType(): typeof Value {
    return this._type || Value;
  }

  // return the type of the result in the case where there is no exception
  static binaryOp(op: BabelBinaryOperator, left: TypesDomain, right: TypesDomain): TypesDomain {
    //todo: goto top only if op === "+"
    let lType = left._type;
    let rType = right._type;
    if (lType === undefined || rType === undefined) return TypesDomain.topVal;
    let resultType = Value;
    switch (op) {
      case "+":
        if (Value.isTypeCompatibleWith(lType, StringValue) || Value.isTypeCompatibleWith(rType, StringValue))
          resultType = StringValue;
        else if (Value.isTypeCompatibleWith(lType, NumberValue) && Value.isTypeCompatibleWith(rType, NumberValue))
          resultType = NumberValue;
        break;
      case "<":
      case ">":
      case ">=":
      case "<=":
      case "!=":
      case "==":
      case "!==":
      case "===":
      case "in":
      case "instanceof":
        resultType = BooleanValue;
        break;
      case ">>>":
      case "<<":
      case ">>":
      case "&":
      case "|":
      case "^":
      case "**":
      case "%":
      case "/":
      case "*":
      case "-":
        resultType = NumberValue;
        break;
      default:
        invariant(false);
    }
    return new TypesDomain(resultType);
  }

  static joinValues(v1: void | Value, v2: void | Value): TypesDomain {
    if (v1 === undefined && v2 === undefined) return new TypesDomain(UndefinedValue);
    if (v1 === undefined || v2 === undefined) return TypesDomain.topVal;
    if (v1 instanceof AbstractValue) return v1.types.joinWith(v2.getType());
    if (v2 instanceof AbstractValue) return v2.types.joinWith(v1.getType());
    return new TypesDomain(v1.getType()).joinWith(v2.getType());
  }

  joinWith(t: typeof Value): TypesDomain {
    let type = this.getType();
    if (type === t) return this;
    if (Value.isTypeCompatibleWith(type, FunctionValue) && Value.isTypeCompatibleWith(t, FunctionValue)) {
      return new TypesDomain(FunctionValue);
    }
    if (Value.isTypeCompatibleWith(type, ObjectValue) && Value.isTypeCompatibleWith(t, ObjectValue)) {
      return new TypesDomain(ObjectValue);
    }
    if (Value.isTypeCompatibleWith(type, PrimitiveValue) && Value.isTypeCompatibleWith(t, PrimitiveValue)) {
      return new TypesDomain(PrimitiveValue);
    }
    return TypesDomain.topVal;
  }

  static logicalOp(op: BabelNodeLogicalOperator, left: TypesDomain, right: TypesDomain): TypesDomain {
    return TypesDomain.joinValues(left, right);
  }

  // return the type of the result in the case where there is no exception
  // note that the type of the operand has no influence on the type of the non exceptional result
  static unaryOp(op: BabelUnaryOperator): TypesDomain {
    let resultType = Value;
    switch (op) {
      case "-":
      case "+":
      case "~":
        resultType = NumberValue;
        break;
      case "!":
      case "delete":
        resultType = BooleanValue;
        break;
      case "typeof":
        resultType = StringValue;
        break;
      case "void":
        resultType = UndefinedValue;
        break;
      default:
        invariant(false);
    }
    return new TypesDomain(resultType);
  }
}
