/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { Realm, Effects } from "../realm.js";
import type { ECMAScriptFunctionValue } from "../values/index.js";
import { AbruptCompletion, JoinedNormalAndAbruptCompletions, SimpleNormalCompletion } from "../completions.js";
import {
  AbstractValue,
  AbstractObjectValue,
  ArrayValue,
  BoundFunctionValue,
  ConcreteValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  ObjectValue,
  PrimitiveValue,
  Value,
} from "../values/index.js";
import invariant from "../invariant.js";
import { Functions, Materialize, Properties, Utils } from "../singletons.js";
import { PropertyDescriptor, cloneDescriptor } from "../descriptors.js";
import { createOperationDescriptor } from "../utils/generator.js";
import { Get } from "../methods/index.js";
import { InternalCall } from "./function.js";
import { valueIsKnownReactAbstraction } from "../react/utils.js";

type OptionalInlinableStatus =
  | "NEEDS_INLINING"
  | "OPTIONALLY_INLINE_WITH_CLONING"
  | "OPTIONALLY_INLINE"
  | "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY";

type LossyConfigProperty =
  | "OBJECT_ABSTRACT_PROPERTIES"
  | "OBJECT_FUNCTION_PROPERTIES"
  | "COMPLEX_ABSTRACT_CONDITIONS"
  | "ARRAY_ABSTRACT_PROPERTIES"
  | "ARRAY_FUNCTION_PROPERTIES";

function checkLossyConfigPropertyEnabled(realm: Realm, property: LossyConfigProperty): boolean {
  if (realm.optionallyInlineFunctionCalls && realm.optionallyInlineFunctionCallsLossyConfig !== undefined) {
    return realm.optionallyInlineFunctionCallsLossyConfig[property] === true;
  }
  return false;
}

function canAvoidPropertyInliningWithLossyConfig(realm: Realm, obj: ObjectValue, propVal: Value): boolean {
  invariant(realm.optionallyInlineFunctionCalls);
  // If the property matches against the below heuristics and we've got the lossy setting on to ignore them
  // if they come back as NEEDS_INLINING, then we ultimately making the property value abstract
  // during the cloning/remodeling phase.
  if (
    propVal instanceof AbstractValue &&
    obj instanceof ArrayValue &&
    obj.$Prototype === realm.intrinsics.ArrayPrototype &&
    checkLossyConfigPropertyEnabled(realm, "ARRAY_ABSTRACT_PROPERTIES")
  ) {
    return true;
  } else if (
    propVal instanceof FunctionValue &&
    obj instanceof ArrayValue &&
    obj.$Prototype === realm.intrinsics.ArrayPrototype &&
    checkLossyConfigPropertyEnabled(realm, "ARRAY_FUNCTION_PROPERTIES")
  ) {
    return true;
  } else if (
    propVal instanceof AbstractValue &&
    obj.$Prototype === realm.intrinsics.ObjectPrototype &&
    checkLossyConfigPropertyEnabled(realm, "OBJECT_ABSTRACT_PROPERTIES")
  ) {
    return true;
  } else if (
    propVal instanceof FunctionValue &&
    obj.$Prototype === realm.intrinsics.ObjectPrototype &&
    checkLossyConfigPropertyEnabled(realm, "OBJECT_FUNCTION_PROPERTIES")
  ) {
    return true;
  }
  return false;
}

function getOptionalInlinableStatus(
  realm: Realm,
  val: Value,
  funcEffects: Effects,
  checkAbstractsAreTemporals: boolean,
  abstractDepth: number
): OptionalInlinableStatus {
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return "OPTIONALLY_INLINE_WITH_CLONING";
    } else if (val instanceof ObjectValue) {
      // If the object was created outside of the function we're trying not to inline, then it's
      // always safe to optimize with this object. Although we return OPTIONALLY_INLINE_WITH_CLONING,
      // the logic inside the cloneOrModelValue will always return the same value if it's been created
      // outside of the function we're trying not to inline.
      if (funcEffects !== undefined && !funcEffects.createdObjects.has(val)) {
        return "OPTIONALLY_INLINE_WITH_CLONING";
      }
      // TODO eventually support temporalAlias, if it's possible
      if (val.temporalAlias !== undefined) {
        return "NEEDS_INLINING";
      }
      if (val.isIntrinsic()) {
        // TODO: are there issues around objects that are intrinsic? I'm not 100% sure.
      }
      if (val.mightBeLeakedObject()) {
        // TODO: are there issues around objects that have leaked? I'm not 100% sure.
      }
      // Check the status of the properties to see if any of them need inlining
      for (let [propName, binding] of val.properties) {
        if (binding && binding.descriptor) {
          // TODO support prototypes and callee
          if (propName === "callee" || propName === "prototype") {
            // Given we don't support cloning functions now, we only check this for other objects
            if (val instanceof FunctionValue) {
              continue;
            }
            invariant(false, "TODO support prototype and callee for non-function objects");
          }
          invariant(val instanceof ObjectValue);
          let propVal = Get(realm, val, propName);
          let propStatus = getOptionalInlinableStatus(
            realm,
            propVal,
            funcEffects,
            checkAbstractsAreTemporals,
            abstractDepth
          );

          if (propStatus === "NEEDS_INLINING" && !canAvoidPropertyInliningWithLossyConfig(realm, val, propVal)) {
            return "NEEDS_INLINING";
          }
        }
      }
      if (val instanceof ArrayValue) {
        if (ArrayValue.isIntrinsicAndHasWidenedNumericProperty(val)) {
          // Needs inlining as it will likely reference a nested optimized function
          // and given this array was created inside the function, there's no
          // real easy way to clone the array and the nested optimized function.
          return "NEEDS_INLINING";
        }
        if (val.$Prototype === realm.intrinsics.ArrayPrototype) {
          return "OPTIONALLY_INLINE_WITH_CLONING";
        }
        return "NEEDS_INLINING";
      } else if (val instanceof FunctionValue) {
        if (val.$Prototype === realm.intrinsics.FunctionPrototype) {
          if (val instanceof ECMAScriptSourceFunctionValue) {
            // TODO support some form of function inlining. It might be too expensive/complex to do other than
            // checking if simple functions have unbound reads to bindings already created in the environment.
            return "NEEDS_INLINING";
          } else if (val instanceof BoundFunctionValue) {
            let thisStatus = getOptionalInlinableStatus(
              realm,
              val.$BoundThis,
              funcEffects,
              checkAbstractsAreTemporals,
              abstractDepth
            );

            if (thisStatus === "NEEDS_INLINING") {
              return "NEEDS_INLINING";
            }
            for (let boundArg of val.$BoundArguments) {
              let boundArgStatus = getOptionalInlinableStatus(
                realm,
                boundArg,
                funcEffects,
                checkAbstractsAreTemporals,
                abstractDepth
              );

              if (boundArgStatus === "NEEDS_INLINING") {
                return "NEEDS_INLINING";
              }
            }
            let targetFunctionStatus = getOptionalInlinableStatus(
              realm,
              val.$BoundTargetFunction,
              funcEffects,
              checkAbstractsAreTemporals,
              abstractDepth
            );

            if (targetFunctionStatus === "NEEDS_INLINING") {
              return "NEEDS_INLINING";
            }
            return "OPTIONALLY_INLINE_WITH_CLONING";
          }
        }
        return "NEEDS_INLINING";
      } else {
        if (val.$Prototype === realm.intrinsics.ObjectPrototype) {
          return "OPTIONALLY_INLINE_WITH_CLONING";
        }
        return "NEEDS_INLINING";
      }
    }
  } else if (val instanceof AbstractValue) {
    if (!funcEffects.createdAbstracts.has(val)) {
      return "OPTIONALLY_INLINE_WITH_CLONING";
    }
    if (valueIsKnownReactAbstraction(realm, val)) {
      // TODO check if all abstractions are always temporal, if they are not
      // we can probably clone/optimize the ones that are not
      return "NEEDS_INLINING";
    }
    if (val.kind === "conditional") {
      let [condValue, consequentVal, alternateVal] = val.args;
      invariant(condValue instanceof AbstractValue);
      let consequentStatus = getOptionalInlinableStatus(
        realm,
        consequentVal,
        funcEffects,
        checkAbstractsAreTemporals,
        abstractDepth + 1 // For conditonals always increase depth
      );
      let alternateStatus = getOptionalInlinableStatus(
        realm,
        alternateVal,
        funcEffects,
        checkAbstractsAreTemporals,
        abstractDepth + 1 // For conditonals always increase depth
      );

      if (
        consequentStatus === "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY" ||
        alternateStatus === "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY"
      ) {
        return "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY";
      } else if (consequentStatus === "NEEDS_INLINING" || alternateStatus === "NEEDS_INLINING") {
        if (checkLossyConfigPropertyEnabled(realm, "COMPLEX_ABSTRACT_CONDITIONS") && abstractDepth > 5) {
          return "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY";
        }
        return "NEEDS_INLINING";
      } else if (consequentStatus === "OPTIONALLY_INLINE" && alternateStatus === "OPTIONALLY_INLINE") {
        return "OPTIONALLY_INLINE";
      } else {
        // We care if the condValue is temporal here, as it means we can't clone the conditional
        let condStatus = getOptionalInlinableStatus(realm, condValue, funcEffects, true, abstractDepth);
        if (condStatus === "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY") {
          return "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY";
        } else if (condStatus === "NEEDS_INLINING") {
          return "NEEDS_INLINING";
        }
        return "OPTIONALLY_INLINE_WITH_CLONING";
      }
    } else if (val.args.length > 0) {
      let optionalInlinableStatus;
      let shouldIncreaseDepth = val.kind === "||" || "&&";

      for (let arg of val.args) {
        // We care if the arg is temporal here, as it means we can't clone the abstract
        let status = getOptionalInlinableStatus(
          realm,
          arg,
          funcEffects,
          checkAbstractsAreTemporals,
          shouldIncreaseDepth ? abstractDepth + 1 : abstractDepth
        );
        if (status === "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY") {
          return "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY";
        } else if (status === "NEEDS_INLINING") {
          if (checkLossyConfigPropertyEnabled(realm, "COMPLEX_ABSTRACT_CONDITIONS") && abstractDepth > 5) {
            return "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY";
          }
          optionalInlinableStatus = "NEEDS_INLINING";
        } else if (status === "OPTIONALLY_INLINE" && optionalInlinableStatus !== "OPTIONALLY_INLINE") {
          optionalInlinableStatus = "NEEDS_INLINING";
        } else if (optionalInlinableStatus !== "NEEDS_INLINING") {
          if (status === "OPTIONALLY_INLINE_WITH_CLONING") {
            optionalInlinableStatus = "OPTIONALLY_INLINE_WITH_CLONING";
          } else if (optionalInlinableStatus === undefined) {
            optionalInlinableStatus = status;
          }
        }
      }
      if (!checkAbstractsAreTemporals && optionalInlinableStatus === "OPTIONALLY_INLINE_WITH_CLONING") {
        // We now re-do the check on the same value, this time failing if any of the args are temporal.
        // We dot this because on the first pass, we want to allow for cases where all args might
        // return "OPTIONALLY_INLINE" without the tempral check in place, meaning we can cosider val
        // as also being "OPTIONALLY_INLINE". Yet, in cases where we don't check for temporals,
        // we may get back "OPTIONALLY_INLINE_WITH_CLONING" where we'd actually get back "NEED_INLING"
        // in the cases where we find abstracts that were temporal.
        let status = getOptionalInlinableStatus(realm, val, funcEffects, true, abstractDepth);
        if (status === "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY") {
          return "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY";
        } else if (status === "NEEDS_INLINING") {
          return "NEEDS_INLINING";
        }
      }
      invariant(optionalInlinableStatus !== undefined);
      return optionalInlinableStatus;
    }
    if (checkAbstractsAreTemporals && val.isTemporal()) {
      return "NEEDS_INLINING";
    }
    if (val instanceof AbstractObjectValue) {
      if (val.values.isTop() || val.values.isBottom()) {
        return "OPTIONALLY_INLINE";
      }
      // TODO check values in values and handle those cases
      return "NEEDS_INLINING";
    }
    // All abstract values with no args are treated as optionally inlinable.
    return "OPTIONALLY_INLINE";
  }
  return "NEEDS_INLINING";
}

function cloneObjectProperties(
  realm: Realm,
  clonedObject: ObjectValue,
  val: ObjectValue,
  intrinsicName: string,
  rootObject: void | ObjectValue,
  funcEffects: Effects
): void {
  clonedObject.refuseSerialization = true;
  for (let [propName, { descriptor }] of val.properties) {
    // TODO support prototypes and callee
    if (propName === "prototype" || propName === "callee") {
      invariant(false, "TODO support prototype and callee");
    }
    invariant(descriptor instanceof PropertyDescriptor);
    let desc = cloneAndModelObjectPropertyDescriptor(
      realm,
      val,
      clonedObject,
      propName,
      descriptor,
      intrinsicName,
      rootObject || clonedObject,
      funcEffects
    );
    Properties.OrdinaryDefineOwnProperty(realm, clonedObject, propName, desc);
  }
  clonedObject.refuseSerialization = false;
}

function applyPostValueConfig(realm: Realm, value: Value, clonedValue: Value, rootObject: void | ObjectValue): void {
  if (clonedValue instanceof ObjectValue) {
    clonedValue.intrinsicNameGenerated = true;
    clonedValue.isScopedTemplate = true;
  }
  if (value instanceof ObjectValue && clonedValue instanceof ObjectValue) {
    if (realm.react.reactProps.has(value)) {
      realm.react.reactProps.add(clonedValue);
    }
    if (value.isPartialObject()) {
      clonedValue.makePartial();
    }
    if (value.isSimpleObject()) {
      clonedValue.makeSimple();
    }
    if (value.mightBeFinalObject()) {
      clonedValue.makeFinal();
    }
  }
  if (rootObject !== undefined) {
    let setOfInlinedObjectProperties = realm.optionallyInlinedDerivedValues.get(rootObject);

    if (setOfInlinedObjectProperties === undefined) {
      setOfInlinedObjectProperties = new Set();
      realm.optionallyInlinedDerivedValues.set(rootObject, setOfInlinedObjectProperties);
    }
    setOfInlinedObjectProperties.add(clonedValue);
  }
}

function isPositiveInteger(str: string) {
  let n = Math.floor(Number(str));
  return n !== Infinity && String(n) === str && n >= 0;
}

function generateDeepIntrinsicName(intrinsicName: string, propName: string) {
  return `${intrinsicName}${isPositiveInteger(propName) ? `[${propName}]` : `.${propName}`}`;
}

function cloneAndModelObjectPropertyDescriptor(
  realm: Realm,
  object: ObjectValue,
  clonedObject: ObjectValue,
  propName: string,
  desc: PropertyDescriptor,
  intrinsicName: string,
  rootObject: void | ObjectValue,
  funcEffects: Effects
): PropertyDescriptor {
  let clonedDesc = cloneDescriptor(desc);
  invariant(clonedDesc !== undefined);
  let propertyIntrinsicName = generateDeepIntrinsicName(intrinsicName, propName);
  if (desc.value !== undefined) {
    let value = desc.value;
    if (value === object) {
      value = clonedObject;
    }
    let clonedValue = cloneAndModelValue(realm, value, propertyIntrinsicName, funcEffects, rootObject);
    clonedDesc.value = clonedValue;
    invariant(realm.createdObjects !== undefined);
    if (
      !(value instanceof PrimitiveValue) &&
      ((value instanceof ObjectValue && realm.createdObjects.has(value)) || value instanceof AbstractValue)
    ) {
      realm.optionallyInlinedDerivedPropertyDependencies.set(clonedValue, clonedObject);
    }
  } else {
    invariant(false, "// TODO handle get/set in cloneAndModelObjectPropertyDescriptor");
  }
  return clonedDesc;
}

function cloneAndModelObjectValue(
  realm: Realm,
  val: ObjectValue,
  intrinsicName: null | string,
  funcEffects: Effects,
  rootObject: void | ObjectValue
): Value {
  // If the value was created inside the funcEffects, then that means we need to clone it
  // otherwise we can just return the value
  if (!funcEffects.createdObjects.has(val)) {
    return val;
  }
  invariant(intrinsicName !== null);
  if (val instanceof ArrayValue) {
    let clonedObject = new ArrayValue(realm, intrinsicName);
    cloneObjectProperties(realm, clonedObject, val, intrinsicName, rootObject, funcEffects);
    applyPostValueConfig(realm, val, clonedObject, rootObject);
    return clonedObject;
  } else if (val instanceof FunctionValue) {
    if (val instanceof BoundFunctionValue) {
      let targetFunction = val.$BoundTargetFunction;
      let clonedTargetFunction = cloneAndModelValue(realm, targetFunction, intrinsicName, funcEffects, rootObject);
      if (clonedTargetFunction instanceof AbstractValue) {
        return clonedTargetFunction;
      }
      invariant(clonedTargetFunction instanceof ECMAScriptSourceFunctionValue);
      let clonedBoundFunction = Functions.BoundFunctionCreate(
        realm,
        clonedTargetFunction,
        val.$BoundThis,
        val.$BoundArguments
      );
      applyPostValueConfig(realm, val, clonedBoundFunction, rootObject);
      return clonedBoundFunction;
    }
    // TODO We do not support functions properly yet
    let abstractalue = AbstractValue.createAbstractArgument(realm, intrinsicName, undefined, val.getType());
    abstractalue.intrinsicName = intrinsicName;
    applyPostValueConfig(realm, val, abstractalue, rootObject);
    return abstractalue;
    // invariant(false, "TODO support function values in cloneAndModelValue");
  } else {
    let clonedObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype, intrinsicName);
    cloneObjectProperties(realm, clonedObject, val, intrinsicName, rootObject, funcEffects);
    applyPostValueConfig(realm, val, clonedObject, rootObject);
    return clonedObject;
  }
}

function cloneAndModelAbstractValue(
  realm: Realm,
  val: AbstractValue,
  intrinsicName: null | string,
  funcEffects: Effects,
  rootObject: void | ObjectValue
): Value {
  if (valueIsKnownReactAbstraction(realm, val)) {
    invariant(false, "we should never hit a React known abstract, they should always be inlined as they are temporal");
  }
  const kind = val.kind;
  if (kind === "conditional") {
    // Conditional ops
    let [condValue, consequentVal, alternateVal] = val.args;
    let clonedCondValue = cloneAndModelValue(realm, condValue, null, funcEffects, rootObject);
    let clonedConsequentVal = cloneAndModelValue(realm, consequentVal, intrinsicName, funcEffects, rootObject);
    let clonedAlternateVal = cloneAndModelValue(realm, alternateVal, intrinsicName, funcEffects, rootObject);
    return AbstractValue.createFromConditionalOp(realm, clonedCondValue, clonedConsequentVal, clonedAlternateVal);
  } else if (kind === "+" || kind === "!=" || kind === "==" || kind === "===" || kind === "!==") {
    // Binary ops
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(realm, leftValue, null, funcEffects, rootObject);
    let clonedRightValue = cloneAndModelValue(realm, rightValue, null, funcEffects, rootObject);
    return AbstractValue.createFromBinaryOp(realm, kind, clonedLeftValue, clonedRightValue);
  } else if (kind === "&&" || kind === "||") {
    // Logical ops
    let [leftValue, rightValue] = val.args;
    let clonedLeftValue = cloneAndModelValue(realm, leftValue, intrinsicName, funcEffects, rootObject);
    let clonedRightValue = cloneAndModelValue(realm, rightValue, intrinsicName, funcEffects, rootObject);
    return AbstractValue.createFromLogicalOp(realm, kind, clonedLeftValue, clonedRightValue);
  } else if (kind === "!" || kind === "typeof" || kind === "delete") {
    // Unary ops
    let [condValue] = val.args;
    let clonedCondValue = cloneAndModelValue(realm, condValue, null, funcEffects, rootObject);
    invariant(val.operationDescriptor !== undefined);
    invariant(clonedCondValue instanceof AbstractValue);
    let hasPrefix = val.operationDescriptor.data.prefix;
    return AbstractValue.createFromUnaryOp(realm, kind, clonedCondValue, hasPrefix);
  }
  invariant(false, "TODO: add functionality to cloneAndModelAbstractValue");
}

function cloneAndModelValue(
  realm: Realm,
  val: Value,
  intrinsicName: null | string,
  funcEffects: Effects,
  rootObject: void | ObjectValue
): Value {
  if (val instanceof ConcreteValue) {
    if (val instanceof PrimitiveValue) {
      return val;
    } else if (val instanceof ObjectValue) {
      return cloneAndModelObjectValue(realm, val, intrinsicName, funcEffects, rootObject);
    }
  } else if (val instanceof AbstractValue) {
    // If the value was created inside the funcEffects, then that means we need to clone it
    // otherwise we can just return the value
    if (!funcEffects.createdAbstracts.has(val)) {
      return val;
    }
    let status = getOptionalInlinableStatus(realm, val, funcEffects, true, 0);
    if (status === "OPTIONALLY_INLINE_WITH_CLONING") {
      return cloneAndModelAbstractValue(realm, val, intrinsicName, funcEffects, rootObject);
    } else {
      invariant(intrinsicName !== null);
      let abstractalue = AbstractValue.createAbstractArgument(realm, intrinsicName, undefined, val.getType());
      abstractalue.intrinsicName = intrinsicName;
      applyPostValueConfig(realm, val, abstractalue, rootObject);
      return abstractalue;
    }
  }
  invariant(false, "cloneValue was passed an unknown type of cloneValue");
}

function createTemporalModeledValue(
  realm: Realm,
  val: Value,
  intrinsicName: void | string,
  temporalArgs: void | Array<Value>,
  rootObject: void | ObjectValue,
  funcEffects: Effects,
  usesThis: boolean
): Value {
  invariant(temporalArgs !== undefined);
  invariant(realm.generator !== undefined);
  if (val instanceof ConcreteValue) {
    return realm.generator.deriveConcreteObjectFromBuildFunction(
      _intrinsicName => {
        let obj = cloneAndModelValue(realm, val, _intrinsicName, funcEffects, undefined);
        invariant(obj instanceof ObjectValue);
        obj.intrinsicName = _intrinsicName;
        return obj;
      },
      temporalArgs,
      createOperationDescriptor("CALL_OPTIONAL_INLINE", { usesThis }),
      // TODO: isPure isn't strictly correct here, as the function
      // might contain abstract function calls that we need to happen
      // and won't happen if the temporal is never referenced (thus DCE).
      { isPure: true }
    );
  } else if (val instanceof AbstractValue) {
    return realm.generator.deriveAbstractFromBuildFunction(
      _intrinsicName => {
        let obj = cloneAndModelValue(realm, val, _intrinsicName, funcEffects, undefined);
        invariant(obj instanceof AbstractValue);
        obj.intrinsicName = _intrinsicName;
        return obj;
      },
      temporalArgs,
      createOperationDescriptor("CALL_OPTIONAL_INLINE", { usesThis }),
      // TODO: isPure isn't strictly correct here, as the function
      // might contain abstract function calls that we need to happen
      // and won't happen if the temporal is never referenced (thus DCE).
      { isPure: true }
    );
  }
  invariant(false, "TODO support more types of abstract value");
}

function createDeepClonedTemporalValue(
  realm: Realm,
  val: Value,
  temporalArgs: Array<Value>,
  funcEffects: Effects,
  usesThis: boolean
): [Value, Effects] {
  let clonedObject;
  let effects = realm.evaluateForEffects(
    () => {
      clonedObject = createTemporalModeledValue(realm, val, undefined, temporalArgs, undefined, funcEffects, usesThis);
      return realm.intrinsics.undefined;
    },
    undefined,
    "createAbstractTemporalValue"
  );
  invariant(clonedObject instanceof Value);
  return [clonedObject, effects];
}

function createAbstractTemporalValue(
  realm: Realm,
  val: Value,
  temporalArgs: Array<Value>,
  usesThis: boolean
): [Value, Effects] {
  let abstractVal;
  let effects = realm.evaluateForEffects(
    () => {
      abstractVal = AbstractValue.createTemporalFromBuildFunction(
        realm,
        val.getType(),
        temporalArgs,
        createOperationDescriptor("CALL_OPTIONAL_INLINE", { usesThis }),
        // TODO: isPure isn't strictly correct here, as the function
        // might contain abstract function calls that we need to happen
        // and won't happen if the temporal is never referenced (thus DCE).
        { isPure: true }
      );
      return realm.intrinsics.undefined;
    },
    undefined,
    "createDeepClonedTemporalValue"
  );
  invariant(abstractVal instanceof AbstractValue);
  return [abstractVal, effects];
}

// If we have a value that is already instrincis and was created outside of the function we're not trying
// to inline then bail-out.
function isValueAnAlreadyDefinedObjectIntrinsic(realm: Realm, val: Value) {
  invariant(realm.createdObjects !== undefined);
  return val instanceof ObjectValue && val.isIntrinsic() && !realm.createdObjects.has(val);
}

export function OptionallyInlineInternalCall(
  realm: Realm,
  F: ECMAScriptFunctionValue,
  thisArgument: Value,
  argsList: Array<Value>
): Value {
  let effects = realm.evaluateForEffects(
    () => InternalCall(realm, F, thisArgument, argsList, 0),
    null,
    "possiblePureFuncCall $Call"
  );
  let result = effects.result;
  if (result instanceof AbruptCompletion) {
    realm.applyEffects(effects);
    throw result;
  } else if (result instanceof JoinedNormalAndAbruptCompletions) {
    // TODO we should support not inlining JoinedNormalAndAbruptCompletions at some point
    return InternalCall(realm, F, thisArgument, argsList, 0);
  } else if (result instanceof SimpleNormalCompletion) {
    result = result.value;
  }
  invariant(result instanceof Value);
  let usesThis = thisArgument !== realm.intrinsics.undefined;
  let args = usesThis ? [thisArgument, ...argsList] : argsList;
  // We always inline primitive values that are returned. There's no apparant benefit from
  // trying to optimize them given they are constant.
  // Furthermore, we do not support "usesThis" just yet, there are some bugs around supporting it
  // that need to get ironed out first. The logic for it remains, as we want to use this in the future.
  if (!usesThis && !(result instanceof PrimitiveValue) && Utils.areEffectsPure(realm, effects, F)) {
    let generator = effects.generator;
    if (generator._entries.length > 0 && !isValueAnAlreadyDefinedObjectIntrinsic(realm, result)) {
      let optimizedValue;
      let optimizedEffects;

      realm.withEffectsAppliedInGlobalEnv(() => {
        invariant(result instanceof Value);
        let status = getOptionalInlinableStatus(realm, result, effects, false, 0);
        if (status === "OPTIONALLY_INLINE" || status === "OPTIONALLY_INLINE_DUE_TO_COMPLEXITY") {
          [optimizedValue, optimizedEffects] = createAbstractTemporalValue(realm, result, [F, ...args], usesThis);
        } else if (status === "OPTIONALLY_INLINE_WITH_CLONING") {
          [optimizedValue, optimizedEffects] = createDeepClonedTemporalValue(
            realm,
            result,
            [F, ...args],
            effects,
            usesThis
          );
        }
        return realm.intrinsics.undefined;
      }, effects);

      if (optimizedValue !== undefined && optimizedEffects !== undefined) {
        // We need to materialize any objects we pass as arguments as objects
        for (let arg of args) {
          if (arg instanceof ObjectValue) {
            Materialize.materializeObject(realm, arg);
          }
        }
        // TODO we need to leak on some of the bindings of F, leaking right now
        // causes failures because we remove much of the value we get from this optimization.
        Materialize.materializeObject(realm, F);
        realm.applyEffects(optimizedEffects);
        return optimizedValue;
      }
    }
  }
  realm.applyEffects(effects);
  return result;
}
