/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { BabelBinaryOperator, BabelNodeLogicalOperator, BabelUnaryOperator } from "babel-types";
import { AbruptCompletion } from "../completions.js";
import { FatalError } from "../errors.js";
import invariant from "../invariant.js";
import {
  AbstractEqualityComparison,
  AbstractRelationalComparison,
  Add,
  HasProperty,
  InstanceofOperator,
  IsCallable,
  StrictEqualityComparison,
  ToBoolean,
  ToInt32,
  ToNumber,
  ToPrimitive,
  ToPropertyKey,
  ToString,
  ToUint32,
} from "../methods/index.js";
import type { Realm } from "../realm.js";
import {
  AbstractValue,
  BooleanValue,
  ConcreteValue,
  EmptyValue,
  NullValue,
  NumberValue,
  ObjectValue,
  StringValue,
  SymbolValue,
  UndefinedValue,
  Value,
} from "../values/index.js";

/* An abstract domain that collects together a set of concrete values
   that might be the value of a variable at runtime.
   Initially, every variable has the value undefined.
   A property that has been weakly deleted will have more than
   one value, one of which will by the EmptyValue.  */

export default class ValuesDomain {
  constructor(values: void | Set<ConcreteValue> | ConcreteValue) {
    if (values instanceof ConcreteValue) {
      let valueSet = new Set();
      valueSet.add(values);
      values = valueSet;
    }
    this._elements = values;
  }

  static topVal = new ValuesDomain(undefined);

  _elements: void | Set<ConcreteValue>;

  isTop() {
    return this._elements === undefined;
  }

  getElements() {
    invariant(this._elements !== undefined);
    return this._elements;
  }

  // return a set of values that may be result of performing the given operation on each pair in the
  // Cartesian product of the value sets of the operands.
  static binaryOp(realm: Realm, op: BabelBinaryOperator, left: ValuesDomain, right: ValuesDomain): ValuesDomain {
    let leftElements = left._elements;
    let rightElements = right._elements;
    // Return top if left and/or right are top or if the size of the value set would get to be quite large.
    // Note: the larger the set of values, the less we know and therefore the less we get value from computing
    // all of these values. TODO #1000: probably the upper bound can be quite a bit smaller.
    if (!leftElements || !rightElements || leftElements.size > 100 || rightElements.size > 100)
      return ValuesDomain.topVal;
    let resultSet = new Set();
    let savedHandler = realm.errorHandler;
    let savedIsReadOnly = realm.isReadOnly;
    realm.isReadOnly = true;
    try {
      realm.errorHandler = () => {
        throw new FatalError();
      };
      for (let leftElem of leftElements) {
        for (let rightElem of rightElements) {
          let result = ValuesDomain.computeBinary(realm, op, leftElem, rightElem);
          invariant(result instanceof ConcreteValue);
          resultSet.add(result);
        }
      }
    } catch (e) {
      if (e instanceof AbruptCompletion) return ValuesDomain.topVal;
    } finally {
      realm.errorHandler = savedHandler;
      realm.isReadOnly = savedIsReadOnly;
    }
    return new ValuesDomain(resultSet);
  }

  // Note that calling this can result in user code running, which can side-effect the heap.
  // If that is not the desired behavior, mark the realm as read-only for the duration of the call.
  static computeBinary(realm: Realm, op: BabelBinaryOperator, lval: ConcreteValue, rval: ConcreteValue): Value {
    if (op === "+") {
      // ECMA262 12.8.3 The Addition Operator
      let lprim = ToPrimitive(realm, lval);
      let rprim = ToPrimitive(realm, rval);

      if (lprim instanceof StringValue || rprim instanceof StringValue) {
        let lstr = ToString(realm, lprim);
        let rstr = ToString(realm, rprim);
        return new StringValue(realm, lstr + rstr);
      }

      let lnum = ToNumber(realm, lprim);
      let rnum = ToNumber(realm, rprim);
      return Add(realm, lnum, rnum);
    } else if (op === "<" || op === ">" || op === ">=" || op === "<=") {
      // ECMA262 12.10.3
      if (op === "<") {
        let r = AbstractRelationalComparison(realm, lval, rval, true);
        if (r instanceof UndefinedValue) {
          return realm.intrinsics.false;
        } else {
          return r;
        }
      } else if (op === "<=") {
        let r = AbstractRelationalComparison(realm, rval, lval, false);
        if (r instanceof UndefinedValue || (r instanceof BooleanValue && r.value)) {
          return realm.intrinsics.false;
        } else {
          return realm.intrinsics.true;
        }
      } else if (op === ">") {
        let r = AbstractRelationalComparison(realm, rval, lval, false);
        if (r instanceof UndefinedValue) {
          return realm.intrinsics.false;
        } else {
          return r;
        }
      } else if (op === ">=") {
        let r = AbstractRelationalComparison(realm, lval, rval, true);
        if (r instanceof UndefinedValue || (r instanceof BooleanValue && r.value)) {
          return realm.intrinsics.false;
        } else {
          return realm.intrinsics.true;
        }
      }
    } else if (op === ">>>") {
      // ECMA262 12.9.5.1
      let lnum = ToUint32(realm, lval);
      let rnum = ToUint32(realm, rval);

      return new NumberValue(realm, lnum >>> rnum);
    } else if (op === "<<" || op === ">>") {
      let lnum = ToInt32(realm, lval);
      let rnum = ToUint32(realm, rval);

      if (op === "<<") {
        // ECMA262 12.9.3.1
        return new NumberValue(realm, lnum << rnum);
      } else if (op === ">>") {
        // ECMA262 12.9.4.1
        return new NumberValue(realm, lnum >> rnum);
      }
    } else if (op === "**") {
      // ECMA262 12.6.3

      // 5. Let base be ? ToNumber(leftValue).
      let base = ToNumber(realm, lval);

      // 6. Let exponent be ? ToNumber(rightValue).
      let exponent = ToNumber(realm, rval);

      // 7. Return the result of Applying the ** operator with base and exponent as specified in 12.7.3.4.
      return new NumberValue(realm, Math.pow(base, exponent));
    } else if (op === "%" || op === "/" || op === "*" || op === "-") {
      // ECMA262 12.7.3
      let lnum = ToNumber(realm, lval);
      let rnum = ToNumber(realm, rval);

      if (isNaN(rnum)) return realm.intrinsics.NaN;
      if (isNaN(lnum)) return realm.intrinsics.NaN;

      if (op === "-") {
        return Add(realm, lnum, rnum, true);
      } else if (op === "%") {
        // The sign of the result equals the sign of the dividend.
        // If the dividend is an infinity, or the divisor is a zero, or both, the result is NaN.
        // If the dividend is finite and the divisor is an infinity, the result equals the dividend.
        // If the dividend is a zero and the divisor is nonzero and finite, the result is the same as the dividend.
        return new NumberValue(realm, lnum % rnum);
      } else if (op === "/") {
        // The sign of the result is positive if both operands have the same sign, negative if the operands have different signs.
        // Division of an infinity by an infinity results in NaN.
        // Division of an infinity by a zero results in an infinity. The sign is determined by the rule already stated above.
        // Division of an infinity by a nonzero finite value results in a signed infinity. The sign is determined by the rule already stated above.
        // Division of a finite value by an infinity results in zero. The sign is determined by the rule already stated above.
        // Division of a zero by a zero results in NaN; division of zero by any other finite value results in zero, with the sign determined by the rule already stated above.
        // Division of a nonzero finite value by a zero results in a signed infinity. The sign is determined by the rule already stated above.
        return new NumberValue(realm, lnum / rnum);
      } else if (op === "*") {
        // The sign of the result is positive if both operands have the same sign, negative if the operands have different signs.
        // Multiplication of an infinity by a zero results in NaN.
        // Multiplication of an infinity by an infinity results in an infinity. The sign is determined by the rule already stated above.
        // Multiplication of an infinity by a finite nonzero value results in a signed infinity. The sign is determined by the rule already stated above.
        return new NumberValue(realm, lnum * rnum);
      }
    } else if (op === "!==") {
      return new BooleanValue(realm, !StrictEqualityComparison(realm, lval, rval));
    } else if (op === "===") {
      return new BooleanValue(realm, StrictEqualityComparison(realm, lval, rval));
    } else if (op === "!=") {
      return new BooleanValue(realm, !AbstractEqualityComparison(realm, lval, rval));
    } else if (op === "==") {
      return new BooleanValue(realm, AbstractEqualityComparison(realm, lval, rval));
    } else if (op === "&" || op === "|" || op === "^") {
      // ECMA262 12.12.3

      // 5. Let lnum be ? ToInt32(lval).
      let lnum: number = ToInt32(realm, lval);

      // 6. Let rnum be ? ToInt32(rval).
      let rnum: number = ToInt32(realm, rval);

      // 7. Return the result of applying the bitwise operator @ to lnum and rnum. The result is a signed 32 bit integer.
      if (op === "&") {
        return new NumberValue(realm, lnum & rnum);
      } else if (op === "|") {
        return new NumberValue(realm, lnum | rnum);
      } else if (op === "^") {
        return new NumberValue(realm, lnum ^ rnum);
      }
    } else if (op === "in") {
      // ECMA262 12.10.3

      // 5. If Type(rval) is not Object, throw a TypeError exception.
      if (!(rval instanceof ObjectValue)) {
        throw new FatalError();
      }

      // 6. Return ? HasProperty(rval, ToPropertyKey(lval)).
      return new BooleanValue(realm, HasProperty(realm, rval, ToPropertyKey(realm, lval)));
    } else if (op === "instanceof") {
      // ECMA262 12.10.3

      // 5. Return ? InstanceofOperator(lval, rval).;
      return new BooleanValue(realm, InstanceofOperator(realm, lval, rval));
    }

    invariant(false, "unimplemented " + op);
  }

  static logicalOp(realm: Realm, op: BabelNodeLogicalOperator, left: ValuesDomain, right: ValuesDomain): ValuesDomain {
    let leftElements = left._elements;
    let rightElements = right._elements;
    // Return top if left and/or right are top or if the size of the value set would get to be quite large.
    // Note: the larger the set of values, the less we know and therefore the less we get value from computing
    // all of these values. TODO #1000: probably the upper bound can be quite a bit smaller.
    if (!leftElements || !rightElements || leftElements.size > 100 || rightElements.size > 100)
      return ValuesDomain.topVal;
    let resultSet = new Set();
    let savedHandler = realm.errorHandler;
    let savedIsReadOnly = realm.isReadOnly;
    realm.isReadOnly = true;
    try {
      realm.errorHandler = () => {
        throw new FatalError();
      };
      for (let leftElem of leftElements) {
        for (let rightElem of rightElements) {
          let result = ValuesDomain.computeLogical(realm, op, leftElem, rightElem);
          invariant(result instanceof ConcreteValue);
          resultSet.add(result);
        }
      }
    } catch (e) {
      if (e instanceof AbruptCompletion) return ValuesDomain.topVal;
    } finally {
      realm.errorHandler = savedHandler;
      realm.isReadOnly = savedIsReadOnly;
    }
    return new ValuesDomain(resultSet);
  }

  // Note that calling this can result in user code running, which can side-effect the heap.
  // If that is not the desired behavior, mark the realm as read-only for the duration of the call.
  static computeLogical(realm: Realm, op: BabelNodeLogicalOperator, lval: ConcreteValue, rval: ConcreteValue): Value {
    let lbool = ToBoolean(realm, lval);

    if (op === "&&") {
      // ECMA262 12.13.3
      if (lbool === false) return lval;
    } else if (op === "||") {
      // ECMA262 12.13.3
      if (lbool === true) return lval;
    }
    return rval;
  }

  // Note that calling this can result in user code running, which can side-effect the heap.
  // If that is not the desired behavior, mark the realm as read-only for the duration of the call.
  static computeUnary(realm: Realm, op: BabelUnaryOperator, value: ConcreteValue): Value {
    if (op === "+") {
      // ECMA262 12.5.6.1
      // 1. Let expr be the result of evaluating UnaryExpression.
      // 2. Return ? ToNumber(? GetValue(expr)).
      return new NumberValue(realm, ToNumber(realm, value));
    } else if (op === "-") {
      // ECMA262 12.5.7.1
      // 1. Let expr be the result of evaluating UnaryExpression.
      // 2. Let oldValue be ? ToNumber(? GetValue(expr)).
      let oldValue = ToNumber(realm, value);

      // 3. If oldValue is NaN, return NaN.
      if (isNaN(oldValue)) {
        return realm.intrinsics.NaN;
      }

      // 4. Return the result of negating oldValue; that is, compute a Number with the same magnitude but opposite sign.
      return new NumberValue(realm, -oldValue);
    } else if (op === "~") {
      // ECMA262 12.5.8
      // 1. Let expr be the result of evaluating UnaryExpression.
      // 2. Let oldValue be ? ToInt32(? GetValue(expr)).
      let oldValue = ToInt32(realm, value);

      // 3. Return the result of applying bitwise complement to oldValue. The result is a signed 32-bit integer.
      return new NumberValue(realm, ~oldValue);
    } else if (op === "!") {
      // ECMA262 12.6.9
      // 1. Let expr be the result of evaluating UnaryExpression.
      // 2. Let oldValue be ToBoolean(? GetValue(expr)).
      let oldValue = ToBoolean(realm, value);

      // 3. If oldValue is true, return false.
      if (oldValue === true) return realm.intrinsics.false;

      // 4. Return true.
      return realm.intrinsics.true;
    } else if (op === "void") {
      // 1. Let expr be the result of evaluating UnaryExpression.
      // 2. Perform ? GetValue(expr).
      // 3. Return undefined.
      return realm.intrinsics.undefined;
    } else if (op === "typeof") {
      function isInstance(proto, Constructor): boolean {
        return proto instanceof Constructor || proto === Constructor.prototype;
      }
      // ECMA262 12.6.5
      // 1. Let val be the result of evaluating UnaryExpression.
      // 2. If Type(val) is Reference, then
      // 3. Let val be ? GetValue(val).
      let val = value;
      // 4. Return a String according to Table 35.
      let proto = val.getType().prototype;
      if (isInstance(proto, UndefinedValue)) {
        return new StringValue(realm, "undefined");
      } else if (isInstance(proto, NullValue)) {
        return new StringValue(realm, "object");
      } else if (isInstance(proto, StringValue)) {
        return new StringValue(realm, "string");
      } else if (isInstance(proto, BooleanValue)) {
        return new StringValue(realm, "boolean");
      } else if (isInstance(proto, NumberValue)) {
        return new StringValue(realm, "number");
      } else if (isInstance(proto, SymbolValue)) {
        return new StringValue(realm, "symbol");
      } else if (isInstance(proto, ObjectValue)) {
        if (IsCallable(realm, val)) {
          return new StringValue(realm, "function");
        }
        return new StringValue(realm, "object");
      } else {
        invariant(false);
      }
    } else {
      invariant(op === "delete");
      // ECMA262 12.5.3.2
      // 1. Let ref be the result of evaluating UnaryExpression.
      // 2. ReturnIfAbrupt(ref).
      // 3. If Type(ref) is not Reference, return true.
      return realm.intrinsics.true;
    }
  }

  static unaryOp(realm: Realm, op: BabelUnaryOperator, operandValues: ValuesDomain): ValuesDomain {
    let operandElements = operandValues._elements;
    if (operandElements === undefined) return ValuesDomain.topVal;
    let resultSet = new Set();
    let savedHandler = realm.errorHandler;
    let savedIsReadOnly = realm.isReadOnly;
    realm.isReadOnly = true;
    try {
      realm.errorHandler = () => {
        throw new FatalError();
      };
      for (let operandElem of operandElements) {
        let result = ValuesDomain.computeUnary(realm, op, operandElem);
        invariant(result instanceof ConcreteValue);
        resultSet.add(result);
      }
    } catch (e) {
      if (e instanceof AbruptCompletion) return ValuesDomain.topVal;
    } finally {
      realm.errorHandler = savedHandler;
      realm.isReadOnly = savedIsReadOnly;
    }
    return new ValuesDomain(resultSet);
  }

  includesValueNotOfType(type: typeof Value): boolean {
    invariant(!this.isTop());
    for (let cval of this.getElements()) {
      if (!(cval instanceof type)) return true;
    }
    return false;
  }

  includesValueOfType(type: typeof Value): boolean {
    invariant(!this.isTop());
    for (let cval of this.getElements()) {
      if (cval instanceof type) return true;
    }
    return false;
  }

  mightBeFalse(): boolean {
    invariant(!this.isTop());
    for (let cval of this.getElements()) {
      if (cval.mightBeFalse()) return true;
    }
    return false;
  }

  mightNotBeFalse(): boolean {
    invariant(!this.isTop());
    for (let cval of this.getElements()) {
      if (cval.mightNotBeFalse()) return true;
    }
    return false;
  }

  static joinValues(realm: Realm, v1: void | Value, v2: void | Value): ValuesDomain {
    if (v1 === undefined) v1 = realm.intrinsics.undefined;
    if (v2 === undefined) v2 = realm.intrinsics.undefined;
    if (v1 instanceof AbstractValue) return v1.values.joinWith(v2);
    if (v2 instanceof AbstractValue) return v2.values.joinWith(v1);
    let union = new Set();
    invariant(v1 instanceof ConcreteValue);
    union.add(v1);
    invariant(v2 instanceof ConcreteValue);
    union.add(v2);
    return new ValuesDomain(union);
  }

  joinWith(y: Value): ValuesDomain {
    if (this.isTop()) return this;
    let union = new Set(this.getElements());
    if (y instanceof AbstractValue) {
      if (y.values.isTop()) return y.values;
      y.values.getElements().forEach(v => union.add(v));
    } else {
      invariant(y instanceof ConcreteValue);
      union.add(y);
    }
    return new ValuesDomain(union);
  }

  static meetValues(realm: Realm, v1: void | Value, v2: void | Value): ValuesDomain {
    if (v1 === undefined) v1 = realm.intrinsics.undefined;
    if (v2 === undefined) v2 = realm.intrinsics.undefined;
    if (v1 instanceof AbstractValue) return v1.values.meetWith(v2);
    if (v2 instanceof AbstractValue) return v2.values.meetWith(v1);
    let intersection = new Set();
    invariant(v1 instanceof ConcreteValue);
    invariant(v2 instanceof ConcreteValue);
    if (v1 === v2) intersection.add(v1);
    return new ValuesDomain(intersection);
  }

  meetWith(y: Value): ValuesDomain {
    let intersection = new Set();
    let elements = this._elements;
    if (y instanceof AbstractValue) {
      if (y.values.isTop()) return this;
      y.values.getElements().forEach(v => {
        if (elements === undefined || elements.has(v)) intersection.add(v);
      });
    } else {
      invariant(y instanceof ConcreteValue);
      if (elements === undefined || elements.has(y)) intersection.add(y);
    }
    return new ValuesDomain(intersection);
  }

  promoteEmptyToUndefined(): ValuesDomain {
    if (this.isTop()) return this;
    let newSet = new Set();
    for (let cval of this.getElements()) {
      if (cval instanceof EmptyValue) newSet.add(cval.$Realm.intrinsics.undefined);
      else newSet.add(cval);
    }
    return new ValuesDomain(newSet);
  }
}
