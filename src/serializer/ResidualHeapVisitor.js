/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { GlobalEnvironmentRecord, DeclarativeEnvironmentRecord } from "../environment.js";
import { FatalError } from "../errors.js";
import { Realm } from "../realm.js";
import type { Descriptor, PropertyBinding, ObjectKind } from "../types.js";
import { HashSet, IsArray, Get } from "../methods/index.js";
import {
  BoundFunctionValue,
  ProxyValue,
  SymbolValue,
  AbstractValue,
  EmptyValue,
  ECMAScriptSourceFunctionValue,
  FunctionValue,
  Value,
  ObjectValue,
  AbstractObjectValue,
  NativeFunctionValue,
  UndefinedValue,
} from "../values/index.js";
import { describeLocation } from "../intrinsics/ecma262/Error.js";
import * as t from "babel-types";
import type { BabelNodeBlockStatement } from "babel-types";
import { Generator } from "../utils/generator.js";
import type { GeneratorEntry, VisitEntryCallbacks } from "../utils/generator.js";
import traverse from "babel-traverse";
import invariant from "../invariant.js";
import type {
  ResidualFunctionBinding,
  FunctionInfo,
  AdditionalFunctionInfo,
  FunctionInstance,
  ClassMethodInstance,
  AdditionalFunctionEffects,
  ReactBytecodeTree,
} from "./types.js";
import { ClosureRefVisitor } from "./visitors.js";
import { Logger } from "../utils/logger.js";
import { Modules } from "../utils/modules.js";
import { ResidualHeapInspector } from "./ResidualHeapInspector.js";
import {
  commonAncestorOf,
  getSuggestedArrayLiteralLength,
  getOrDefault,
  ClassPropertiesToIgnore,
  withDescriptorValue,
  canIgnoreClassLengthProperty,
} from "./utils.js";
import { Environment, To } from "../singletons.js";
import { isReactElement, valueIsReactLibraryObject } from "../react/utils.js";
import { canHoistReactElement } from "../react/hoisting.js";
import ReactElementSet from "../react/ReactElementSet.js";
import { withBytecodeComponentEffects } from "../react/bytecode.js";

export type Scope = FunctionValue | Generator;

/* This class visits all values that are reachable in the residual heap.
   In particular, this "filters out" values that are:
   - captured by a DeclarativeEnvironmentRecord, but not actually used by any closure.
   - Unmodified prototype objects
   TODO #680: Figure out minimal set of values that need to be kept alive for WeakSet and WeakMap instances.
*/
export class ResidualHeapVisitor {
  constructor(
    realm: Realm,
    logger: Logger,
    modules: Modules,
    additionalFunctionValuesAndEffects: Map<FunctionValue, AdditionalFunctionEffects>,
    reactFunctionToBytecodeTrees: Map<FunctionValue, ReactBytecodeTree>
  ) {
    invariant(realm.useAbstractInterpretation);
    this.realm = realm;
    this.logger = logger;
    this.modules = modules;

    this.declarativeEnvironmentRecordsBindings = new Map();
    this.globalBindings = new Map();
    this.functionInfos = new Map();
    this.classMethodInstances = new Map();
    this.functionInstances = new Map();
    this.values = new Map();
    let generator = this.realm.generator;
    invariant(generator);
    this.scope = this.commonScope = generator;
    this.inspector = new ResidualHeapInspector(realm, logger);
    this.referencedDeclaredValues = new Set();
    this.delayedVisitGeneratorEntries = [];
    this.shouldVisitReactLibrary = false;
    this.additionalFunctionValuesAndEffects = additionalFunctionValuesAndEffects;
    this.reactFunctionToBytecodeTrees = reactFunctionToBytecodeTrees;
    this.equivalenceSet = new HashSet();
    this.reactElementEquivalenceSet = new ReactElementSet(realm, this.equivalenceSet);
    this.additionalFunctionValueInfos = new Map();
    this.inAdditionalFunction = false;
    this.additionalRoots = new Set();
    this.reactBytecodeTrees = new Map();
  }

  realm: Realm;
  logger: Logger;
  modules: Modules;

  // Caches that ensure one ResidualFunctionBinding exists per (record, name) pair
  declarativeEnvironmentRecordsBindings: Map<DeclarativeEnvironmentRecord, Map<string, ResidualFunctionBinding>>;
  globalBindings: Map<string, ResidualFunctionBinding>;

  functionInfos: Map<BabelNodeBlockStatement, FunctionInfo>;
  scope: Scope;
  // Either the realm's generator or the FunctionValue of an additional function to serialize
  commonScope: Scope;
  values: Map<Value, Set<Scope>>;
  inspector: ResidualHeapInspector;
  referencedDeclaredValues: Set<AbstractValue>;
  delayedVisitGeneratorEntries: Array<{| commonScope: Scope, generator: Generator, entry: GeneratorEntry |}>;
  additionalFunctionValuesAndEffects: Map<FunctionValue, AdditionalFunctionEffects>;
  functionInstances: Map<FunctionValue, FunctionInstance>;
  additionalFunctionValueInfos: Map<FunctionValue, AdditionalFunctionInfo>;
  reactFunctionToBytecodeTrees: Map<FunctionValue, ReactBytecodeTree>;
  equivalenceSet: HashSet<AbstractValue>;
  classMethodInstances: Map<FunctionValue, ClassMethodInstance>;
  shouldVisitReactLibrary: boolean;
  reactElementEquivalenceSet: ReactElementSet;
  reactBytecodeTrees: Map<ObjectValue, ReactBytecodeTree>;

  // We only want to add to additionalRoots when we're in an additional function
  inAdditionalFunction: boolean;
  // Tracks objects + functions that were visited from inside additional functions that need to be serialized in a
  // parent scope of the additional function (e.g. functions/objects only used from additional functions that were
  // declared outside the additional function need to be serialized in the additional function's parent scope for
  // identity to work).
  additionalRoots: Set<ObjectValue>;

  _withScope(scope: Scope, f: () => void) {
    let oldScope = this.scope;
    this.scope = scope;
    f();
    this.scope = oldScope;
  }

  visitObjectProperty(binding: PropertyBinding) {
    let desc = binding.descriptor;
    if (desc === undefined) return; //deleted
    let obj = binding.object;
    if (obj instanceof AbstractObjectValue || !this.inspector.canIgnoreProperty(obj, binding.key)) {
      this.visitDescriptor(desc);
    }
  }

  visitObjectProperties(obj: ObjectValue, kind?: ObjectKind): void {
    // visit properties
    if (kind !== "ReactElement") {
      for (let [symbol, propertyBinding] of obj.symbols) {
        invariant(propertyBinding);
        let desc = propertyBinding.descriptor;
        if (desc === undefined) continue; //deleted
        this.visitDescriptor(desc);
        this.visitValue(symbol);
      }
    }

    // visit properties
    for (let [propertyBindingKey, propertyBindingValue] of obj.properties) {
      // we don't want to the $$typeof or _owner/_store properties
      // as this is contained within the JSXElement, otherwise
      // they we be need to be emitted during serialization
      if (
        kind === "ReactElement" &&
        (propertyBindingKey === "$$typeof" || propertyBindingKey === "_owner" || propertyBindingKey === "_store")
      ) {
        continue;
      }
      // we don't want to visit these as we handle the serialization ourselves
      // via a different logic route for classes
      if (
        obj.$FunctionKind === "classConstructor" &&
        (propertyBindingKey === "arguments" ||
          propertyBindingKey === "length" ||
          propertyBindingKey === "name" ||
          propertyBindingKey === "caller")
      ) {
        continue;
      }
      if (propertyBindingKey.pathNode !== undefined) continue; // property is written to inside a loop
      invariant(propertyBindingValue);
      this.visitObjectProperty(propertyBindingValue);
    }

    // inject properties with computed names
    if (obj.unknownProperty !== undefined) {
      let desc = obj.unknownProperty.descriptor;
      if (desc !== undefined) {
        let val = desc.value;
        invariant(val instanceof AbstractValue);
        this.visitObjectPropertiesWithComputedNames(val);
      }
    }

    // prototype
    if (kind !== "ReactElement") {
      // we don't want to the ReactElement prototype visited
      // as this is contained within the JSXElement, otherwise
      // they we be need to be emitted during serialization
      this.visitObjectPrototype(obj);
    }
    if (obj instanceof FunctionValue) this.visitConstructorPrototype(obj);
  }

  visitObjectPrototype(obj: ObjectValue) {
    let proto = obj.$Prototype;

    let kind = obj.getKind();
    if (proto === this.realm.intrinsics[kind + "Prototype"]) return;

    if (!obj.$IsClassPrototype || proto !== this.realm.intrinsics.null) {
      this.visitValue(proto);
    }
  }

  visitConstructorPrototype(func: FunctionValue) {
    // If the original prototype object was mutated,
    // request its serialization here as this might be observable by
    // residual code.
    let prototype = ResidualHeapInspector.getPropertyValue(func, "prototype");
    if (
      prototype instanceof ObjectValue &&
      prototype.originalConstructor === func &&
      !this.inspector.isDefaultPrototype(prototype)
    ) {
      this.visitValue(prototype);
    }
  }

  visitObjectPropertiesWithComputedNames(absVal: AbstractValue): void {
    if (absVal.kind === "widened property") return;
    invariant(absVal.args.length === 3);
    let cond = absVal.args[0];
    invariant(cond instanceof AbstractValue);
    if (cond.kind === "template for property name condition") {
      let P = cond.args[0];
      invariant(P instanceof AbstractValue);
      let V = absVal.args[1];
      let earlier_props = absVal.args[2];
      if (earlier_props instanceof AbstractValue) this.visitObjectPropertiesWithComputedNames(earlier_props);
      this.visitValue(P);
      this.visitValue(V);
    } else {
      // conditional assignment
      absVal.args[0] = this.visitEquivalentValue(cond);
      let consequent = absVal.args[1];
      invariant(consequent instanceof AbstractValue);
      let alternate = absVal.args[2];
      invariant(alternate instanceof AbstractValue);
      this.visitObjectPropertiesWithComputedNames(consequent);
      this.visitObjectPropertiesWithComputedNames(alternate);
    }
  }

  visitDescriptor(desc: Descriptor): void {
    invariant(desc.value === undefined || desc.value instanceof Value);
    if (desc.joinCondition !== undefined) {
      desc.joinCondition = this.visitEquivalentValue(desc.joinCondition);
      if (desc.descriptor1 !== undefined) this.visitDescriptor(desc.descriptor1);
      if (desc.descriptor2 !== undefined) this.visitDescriptor(desc.descriptor2);
      return;
    }
    if (desc.value !== undefined) desc.value = this.visitEquivalentValue(desc.value);
    if (desc.get !== undefined) this.visitValue(desc.get);
    if (desc.set !== undefined) this.visitValue(desc.set);
  }

  visitValueArray(val: ObjectValue): void {
    this.visitObjectProperties(val);
    const realm = this.realm;
    let lenProperty = Get(realm, val, "length");
    if (
      lenProperty instanceof AbstractValue ||
      To.ToLength(realm, lenProperty) !== getSuggestedArrayLiteralLength(realm, val)
    ) {
      this.visitValue(lenProperty);
    }
  }

  visitValueMap(val: ObjectValue): void {
    let kind = val.getKind();

    let entries;
    if (kind === "Map") {
      entries = val.$MapData;
    } else {
      invariant(kind === "WeakMap");
      entries = val.$WeakMapData;
    }
    invariant(entries !== undefined);
    let len = entries.length;

    for (let i = 0; i < len; i++) {
      let entry = entries[i];
      let key = entry.$Key;
      let value = entry.$Value;
      if (key === undefined || value === undefined) continue;
      this.visitValue(key);
      this.visitValue(value);
    }
  }

  visitValueSet(val: ObjectValue): void {
    let kind = val.getKind();

    let entries;
    if (kind === "Set") {
      entries = val.$SetData;
    } else {
      invariant(kind === "WeakSet");
      entries = val.$WeakSetData;
    }
    invariant(entries !== undefined);
    let len = entries.length;

    for (let i = 0; i < len; i++) {
      let entry = entries[i];
      if (entry === undefined) continue;
      this.visitValue(entry);
    }
  }

  visitValueFunction(val: FunctionValue, parentScope: Scope): void {
    if (this.inAdditionalFunction) this.additionalRoots.add(val);
    this.visitObjectProperties(val);

    if (val instanceof BoundFunctionValue) {
      this.visitValue(val.$BoundTargetFunction);
      this.visitValue(val.$BoundThis);
      for (let boundArg of val.$BoundArguments) this.visitValue(boundArg);
      return;
    }

    invariant(!(val instanceof NativeFunctionValue), "all native function values should be intrinsics");

    invariant(val instanceof ECMAScriptSourceFunctionValue);
    invariant(val.constructor === ECMAScriptSourceFunctionValue);
    let formalParameters = val.$FormalParameters;
    let code = val.$ECMAScriptCode;

    let functionInfo = this.functionInfos.get(code);
    let residualFunctionBindings = new Map();
    this.functionInstances.set(val, {
      residualFunctionBindings,
      initializationStatements: [],
      functionValue: val,
      scopeInstances: new Map(),
    });

    if (!functionInfo) {
      functionInfo = {
        unbound: new Set(),
        modified: new Set(),
        usesArguments: false,
        usesThis: false,
      };
      let state = {
        tryQuery: this.logger.tryQuery.bind(this.logger),
        val,
        functionInfo,
        realm: this.realm,
      };
      traverse(
        t.file(t.program([t.expressionStatement(t.functionExpression(null, formalParameters, code))])),
        ClosureRefVisitor,
        null,
        state
      );
      this.functionInfos.set(code, functionInfo);

      if (val.isResidual && functionInfo.unbound.size) {
        if (!val.isUnsafeResidual) {
          this.logger.logError(
            val,
            `residual function ${describeLocation(this.realm, val, undefined, code.loc) ||
              "(unknown)"} refers to the following identifiers defined outside of the local scope: ${Object.keys(
              functionInfo.unbound
            ).join(", ")}`
          );
        }
      }
    }

    let additionalFunctionEffects = this.additionalFunctionValuesAndEffects.get(val);
    if (additionalFunctionEffects) {
      this._visitAdditionalFunction(val, additionalFunctionEffects, parentScope);
    } else {
      this._withScope(val, () => {
        invariant(functionInfo);
        for (let innerName of functionInfo.unbound) {
          let residualBinding = this.visitBinding(val, innerName);
          invariant(residualBinding !== undefined);
          residualFunctionBindings.set(innerName, residualBinding);
          if (functionInfo.modified.has(innerName)) {
            residualBinding.modified = true;
          }
        }
      });
    }
    if (val.$FunctionKind === "classConstructor") {
      let homeObject = val.$HomeObject;
      if (homeObject instanceof ObjectValue && homeObject.$IsClassPrototype) {
        this._visitClass(val, homeObject);
      }
    }
    this.functionInstances.set(val, {
      residualFunctionBindings,
      initializationStatements: [],
      functionValue: val,
      scopeInstances: new Map(),
    });
  }

  // Visits a binding, if createBinding is true, will always return a ResidualFunctionBinding
  // otherwise visits + returns the binding only if one already exists.
  visitBinding(val: FunctionValue, name: string, createBinding: boolean = true): ResidualFunctionBinding | void {
    let residualFunctionBinding;
    let doesNotMatter = true;
    let reference = this.logger.tryQuery(
      () => Environment.ResolveBinding(this.realm, name, doesNotMatter, val.$Environment),
      undefined,
      false /* The only reason `ResolveBinding` might fail is because the global object is partial. But in that case, we know that we are dealing with the common scope. */
    );
    let getFromMap = createBinding ? getOrDefault : (map, key, defaultFn) => map.get(key);
    if (
      reference === undefined ||
      Environment.IsUnresolvableReference(this.realm, reference) ||
      reference.base instanceof GlobalEnvironmentRecord
    ) {
      // Global Binding
      residualFunctionBinding = getFromMap(
        this.globalBindings,
        name,
        () =>
          ({
            value: this.realm.getGlobalLetBinding(name),
            modified: true,
            declarativeEnvironmentRecord: null,
          }: ResidualFunctionBinding)
      );
    } else {
      // DeclarativeEnvironmentRecord binding
      invariant(!Environment.IsUnresolvableReference(this.realm, reference));
      let referencedBase = reference.base;
      let referencedName: string = (reference.referencedName: any);
      if (typeof referencedName !== "string") {
        throw new FatalError("TODO: do not know how to visit reference with symbol");
      }
      invariant(referencedBase instanceof DeclarativeEnvironmentRecord);
      let residualFunctionBindings = getOrDefault(
        this.declarativeEnvironmentRecordsBindings,
        referencedBase,
        () => new Map()
      );
      residualFunctionBinding = getFromMap(residualFunctionBindings, referencedName, (): ResidualFunctionBinding => {
        invariant(referencedBase instanceof DeclarativeEnvironmentRecord);
        let binding = referencedBase.bindings[referencedName];
        invariant(!binding.deletable);
        return {
          value: (binding.initialized && binding.value) || this.realm.intrinsics.undefined,
          modified: false,
          declarativeEnvironmentRecord: referencedBase,
        };
      });
    }
    if (residualFunctionBinding && residualFunctionBinding.value) {
      residualFunctionBinding.value = this.visitEquivalentValue(residualFunctionBinding.value);
    }
    return residualFunctionBinding;
  }

  _visitClass(classFunc: ECMAScriptSourceFunctionValue, classPrototype: ObjectValue): void {
    let visitClassMethod = (propertyNameOrSymbol, methodFunc, methodType, isStatic) => {
      if (methodFunc instanceof ECMAScriptSourceFunctionValue) {
        // if the method does not have a $HomeObject, it's not a class method
        if (methodFunc.$HomeObject !== undefined) {
          if (methodFunc !== classFunc) {
            this._visitClassMethod(methodFunc, methodType, classPrototype, !!isStatic);
          }
        }
      }
    };
    for (let [propertyName, method] of classPrototype.properties) {
      withDescriptorValue(propertyName, method.descriptor, visitClassMethod);
    }
    for (let [symbol, method] of classPrototype.symbols) {
      withDescriptorValue(symbol, method.descriptor, visitClassMethod);
    }
    if (classPrototype.properties.has("constructor")) {
      let constructor = classPrototype.properties.get("constructor");

      invariant(constructor !== undefined);
      // check if the constructor was deleted, as it can't really be deleted
      // it just gets set to empty (the default again)
      if (constructor.descriptor === undefined) {
        classFunc.$HasEmptyConstructor = true;
      } else {
        let visitClassProperty = (propertyNameOrSymbol, methodFunc, methodType) => {
          visitClassMethod(propertyNameOrSymbol, methodFunc, methodType, true);
        };
        // check if we have any static methods we need to include
        let constructorFunc = Get(this.realm, classPrototype, "constructor");
        invariant(constructorFunc instanceof ObjectValue);
        for (let [propertyName, method] of constructorFunc.properties) {
          if (
            !ClassPropertiesToIgnore.has(propertyName) &&
            method.descriptor !== undefined &&
            !(
              propertyName === "length" && canIgnoreClassLengthProperty(constructorFunc, method.descriptor, this.logger)
            )
          ) {
            withDescriptorValue(propertyName, method.descriptor, visitClassProperty);
          }
        }
      }
    }
    this.classMethodInstances.set(classFunc, {
      classPrototype,
      methodType: "constructor",
      classSuperNode: undefined,
      classMethodIsStatic: false,
      classMethodKeyNode: undefined,
      classMethodComputed: false,
    });
  }

  _visitClassMethod(
    methodFunc: ECMAScriptSourceFunctionValue,
    methodType: "get" | "set" | "value",
    classPrototype: ObjectValue,
    isStatic: boolean
  ): void {
    this.classMethodInstances.set(methodFunc, {
      classPrototype,
      methodType: methodType === "value" ? "method" : methodType,
      classSuperNode: undefined,
      classMethodIsStatic: isStatic,
      classMethodKeyNode: undefined,
      classMethodComputed: !!methodFunc.$HasComputedName,
    });
  }

  visitValueObject(val: ObjectValue): void {
    if (this.inAdditionalFunction) this.additionalRoots.add(val);
    let kind = val.getKind();
    this.visitObjectProperties(val, kind);

    // If this object is a prototype object that was implicitly created by the runtime
    // for a constructor, then we can obtain a reference to this object
    // in a special way that's handled alongside function serialization.
    let constructor = val.originalConstructor;
    if (constructor !== undefined) {
      this.visitValue(constructor);
      return;
    }

    switch (kind) {
      case "RegExp":
      case "Number":
      case "String":
      case "Boolean":
      case "ArrayBuffer":
        return;
      case "ReactElement":
        this.shouldVisitReactLibrary = true;
        // check we can hoist a React Element
        canHoistReactElement(this.realm, val, this);
        return;
      case "Date":
        let dateValue = val.$DateValue;
        invariant(dateValue !== undefined);
        this.visitValue(dateValue);
        return;
      case "Float32Array":
      case "Float64Array":
      case "Int8Array":
      case "Int16Array":
      case "Int32Array":
      case "Uint8Array":
      case "Uint16Array":
      case "Uint32Array":
      case "Uint8ClampedArray":
      case "DataView":
        let buf = val.$ViewedArrayBuffer;
        invariant(buf !== undefined);
        this.visitValue(buf);
        return;
      case "Map":
      case "WeakMap":
        this.visitValueMap(val);
        return;
      case "Set":
      case "WeakSet":
        this.visitValueSet(val);
        return;
      default:
        if (kind !== "Object") this.logger.logError(val, `Object of kind ${kind} is not supported in residual heap.`);
        if (this.$ParameterMap !== undefined) {
          this.logger.logError(val, `Arguments object is not supported in residual heap.`);
        }
        if (this.realm.react.enabled && valueIsReactLibraryObject(this.realm, val, this.logger)) {
          this.realm.react.reactLibraryObject = val;
        }
        return;
    }
  }

  visitValueSymbol(val: SymbolValue): void {
    if (val.$Description) this.visitValue(val.$Description);
  }

  visitValueProxy(val: ProxyValue): void {
    this.visitValue(val.$ProxyTarget);
    this.visitValue(val.$ProxyHandler);
  }

  visitAbstractValue(val: AbstractValue): void {
    if (val.kind === "sentinel member expression")
      this.logger.logError(val, "expressions of type o[p] are not yet supported for partially known o and unknown p");
    if (val.kind === "sentinel ToObject") this.logger.logError(val, "Unknown object cannot be coerced to Object");
    for (let i = 0, n = val.args.length; i < n; i++) {
      val.args[i] = this.visitEquivalentValue(val.args[i]);
    }
  }

  // Overridable hook for pre-visiting the value.
  // Return false will tell visitor to skip visiting children of this node.
  preProcessValue(val: Value): boolean {
    return this._mark(val);
  }

  // Overridable hook for post-visiting the value.
  postProcessValue(val: Value) {}

  _mark(val: Value): boolean {
    let scopes = this.values.get(val);
    if (scopes === undefined) this.values.set(val, (scopes = new Set()));
    if (scopes.has(this.scope)) return false;
    scopes.add(this.scope);
    return true;
  }

  visitEquivalentValue<T: Value>(val: T): T {
    if (val instanceof AbstractValue) {
      let equivalentValue = this.equivalenceSet.add(val);
      if (this.preProcessValue(equivalentValue)) this.visitAbstractValue(equivalentValue);
      this.postProcessValue(equivalentValue);
      return (equivalentValue: any);
    } else if (val instanceof FunctionValue && this.reactFunctionToBytecodeTrees.has(val)) {
      let reactBytecodeTree = this.reactFunctionToBytecodeTrees.get(val);
      invariant(reactBytecodeTree);
      return (this._visitReactBytecodeTree(reactBytecodeTree): any);
    }
    if (val instanceof ObjectValue && isReactElement(val)) {
      let equivalentReactElementValue = this.reactElementEquivalenceSet.add(val);
      if (this._mark(equivalentReactElementValue)) this.visitValueObject(equivalentReactElementValue);
      return (equivalentReactElementValue: any);
    }
    this.visitValue(val);
    return val;
  }

  visitValue(val: Value): void {
    invariant(!val.refuseSerialization);
    if (val instanceof AbstractValue) {
      if (this.preProcessValue(val)) this.visitAbstractValue(val);
    } else if (val.isIntrinsic()) {
      // All intrinsic values exist from the beginning of time...
      // ...except for a few that come into existence as templates for abstract objects (TODO #882).
      if (val.isTemplate) this.preProcessValue(val);
      else
        this._withScope(this.commonScope, () => {
          this.preProcessValue(val);
        });
    } else if (val instanceof EmptyValue) {
      this.preProcessValue(val);
    } else if (ResidualHeapInspector.isLeaf(val)) {
      this.preProcessValue(val);
    } else if (IsArray(this.realm, val)) {
      invariant(val instanceof ObjectValue);
      if (this.preProcessValue(val)) this.visitValueArray(val);
    } else if (val instanceof ProxyValue) {
      if (this.preProcessValue(val)) this.visitValueProxy(val);
    } else if (val instanceof FunctionValue) {
      // Function declarations should get hoisted in common scope so that instances only get allocated once
      let parentScope = this.scope;
      this._withScope(this.commonScope, () => {
        invariant(val instanceof FunctionValue);
        if (this.preProcessValue(val)) this.visitValueFunction(val, parentScope);
      });
    } else if (val instanceof SymbolValue) {
      if (this.preProcessValue(val)) this.visitValueSymbol(val);
    } else {
      invariant(val instanceof ObjectValue);

      // Prototypes are reachable via function declarations, and those get hoisted, so we need to move
      // prototype initialization to the common scope code as well.
      if (val.originalConstructor !== undefined) {
        this._withScope(this.commonScope, () => {
          invariant(val instanceof ObjectValue);
          if (this.preProcessValue(val)) this.visitValueObject(val);
        });
      } else {
        if (this.preProcessValue(val)) this.visitValueObject(val);
      }
    }
    this.postProcessValue(val);
  }

  createGeneratorVisitCallbacks(generator: Generator, commonScope: Scope): VisitEntryCallbacks {
    return {
      visitValues: (values: Array<Value>) => {
        for (let i = 0, n = values.length; i < n; i++) values[i] = this.visitEquivalentValue(values[i]);
      },
      visitGenerator: this.visitGenerator.bind(this),
      canSkip: (value: AbstractValue): boolean => {
        return !this.referencedDeclaredValues.has(value) && !this.values.has(value);
      },
      recordDeclaration: (value: AbstractValue) => {
        this.referencedDeclaredValues.add(value);
      },
      recordDelayedEntry: (entry: GeneratorEntry) => {
        this.delayedVisitGeneratorEntries.push({ commonScope, generator, entry });
      },
    };
  }

  visitGenerator(generator: Generator): void {
    this._withScope(generator, () => {
      generator.visit(this.createGeneratorVisitCallbacks(generator, this.commonScope));
    });
  }

  _visitReactBytecodeTree(reactBytecodeTree: ReactBytecodeTree) {
    let { rootBytecodeComponent } = reactBytecodeTree;
    let { effects, instructions, nodeValue, values } = rootBytecodeComponent;

    return withBytecodeComponentEffects(this.realm, effects, generator => {
      this.visitValue(instructions);
      this.visitGenerator(generator);
      for (let value of values) {
        this.visitValue(value);
      }
      this.visitValue(nodeValue);
      this.reactBytecodeTrees.set(rootBytecodeComponent.nodeValue, reactBytecodeTree);
      return rootBytecodeComponent.nodeValue;
    });
  }

  _visitAdditionalFunction(
    functionValue: FunctionValue,
    additionalEffects: AdditionalFunctionEffects,
    parentScope: Scope
  ) {
    // Get Instance + Info
    invariant(functionValue instanceof ECMAScriptSourceFunctionValue);
    let code = functionValue.$ECMAScriptCode;
    let functionInfo = this.functionInfos.get(code);
    invariant(functionInfo !== undefined);
    let funcInstance = this.functionInstances.get(functionValue);
    invariant(funcInstance !== undefined);

    // Set Visitor state
    // Allows us to emit function declarations etc. inside of this additional
    // function instead of adding them at global scope
    let prevCommonScope = this.commonScope;
    this.commonScope = functionValue;
    let oldReactElementEquivalenceSet = this.reactElementEquivalenceSet;
    this.reactElementEquivalenceSet = new ReactElementSet(this.realm, this.equivalenceSet);
    let oldInAdditionalFunction = this.inAdditionalFunction;
    this.inAdditionalFunction = true;
    let prevReVisit = this.additionalRoots;
    this.additionalRoots = new Set();

    let _visitAdditionalFunctionEffects = () => {
      let { effects } = additionalEffects;
      let [
        result,
        generator,
        modifiedBindings,
        modifiedProperties: Map<PropertyBinding, void | Descriptor>,
        createdObjects,
      ] = effects;
      // Need to do this fixup because otherwise we will skip over this function's
      // generator in the _getTarget scope lookup
      generator.parent = functionValue.parent;
      functionValue.parent = generator;
      // result -- ignore TODO: return the result from the function somehow
      // Generator -- visit all entries
      // Bindings -- (modifications to named variables) only need to serialize bindings if they're
      //             captured by a residual function
      //          -- need to apply them and maybe need to revisit functions in ancestors to make sure
      //             we don't overwrite anything they capture
      //          -- TODO: deal with these properly
      // PropertyBindings -- (property modifications) visit any property bindings to pre-existing objects
      // CreatedObjects -- should take care of itself
      this.realm.applyEffects([
        result,
        new Generator(this.realm),
        modifiedBindings,
        modifiedProperties,
        createdObjects,
      ]);
      let modifiedBindingInfo = new Map();
      let visitPropertiesAndBindings = () => {
        for (let propertyBinding of modifiedProperties.keys()) {
          let binding: PropertyBinding = ((propertyBinding: any): PropertyBinding);
          let object = binding.object;
          if (object instanceof ObjectValue && createdObjects.has(object)) continue; // Created Object's binding
          if (object.refuseSerialization) continue; // modification to internal state
          if (object.intrinsicName === "global") continue; // Avoid double-counting
          this.visitObjectProperty(binding);
        }
        // Handing of ModifiedBindings
        for (let [additionalBinding, previousValue] of modifiedBindings) {
          let modifiedBinding = additionalBinding;
          let residualBinding;
          this._withScope(functionValue, () => {
            // Also visit the original value of the binding
            residualBinding = this.visitBinding(functionValue, modifiedBinding.name);
            invariant(residualBinding !== undefined);
            // Fixup the binding to have the correct value
            // No previousValue means this is a binding for a nested function
            if (previousValue && previousValue.value)
              residualBinding.value = this.visitEquivalentValue(previousValue.value);
            invariant(functionInfo !== undefined);
            if (functionInfo.modified.has(modifiedBinding.name)) residualBinding.modified;
          });
          invariant(residualBinding !== undefined);
          invariant(funcInstance !== undefined);
          funcInstance.residualFunctionBindings.set(modifiedBinding.name, residualBinding);
          let newValue = modifiedBinding.value;
          invariant(newValue);
          this.visitValue(newValue);
          residualBinding.modified = true;
          // This should be enforced by checkThatFunctionsAreIndependent
          invariant(
            !residualBinding.additionalFunctionOverridesValue,
            "We should only have one additional function value modifying any given residual binding"
          );
          if (previousValue && previousValue.value) residualBinding.additionalFunctionOverridesValue = functionValue;
          modifiedBindingInfo.set(modifiedBinding, residualBinding);
        }
        invariant(result instanceof Value);
        if (!(result instanceof UndefinedValue)) this.visitValue(result);
      };
      invariant(funcInstance !== undefined);
      invariant(functionInfo !== undefined);
      this.additionalFunctionValueInfos.set(functionValue, {
        functionValue,
        captures: functionInfo.unbound,
        modifiedBindings: modifiedBindingInfo,
        instance: funcInstance,
      });
      this.visitGenerator(generator);
      // All modified properties and bindings should be accessible
      // from its containing additional function scope.
      this._withScope(functionValue, visitPropertiesAndBindings);

      // Remove any modifications to CreatedObjects -- these are fine being serialized inside the additional function
      this.additionalRoots = new Set([...this.additionalRoots].filter(x => !createdObjects.has(x)));
      this.realm.restoreBindings(modifiedBindings);
      this.realm.restoreProperties(modifiedProperties);
      return this.realm.intrinsics.undefined;
    };
    this.realm.evaluateAndRevertInGlobalEnv(_visitAdditionalFunctionEffects);

    // Cleanup
    this.commonScope = prevCommonScope;
    this.reactElementEquivalenceSet = oldReactElementEquivalenceSet;
    this._withScope(
      parentScope,
      // Re-visit any bindings corresponding to unbound values or values closed over from outside additional function
      // they're serialized in the correct scope
      () => {
        invariant(functionInfo !== undefined);
        invariant(funcInstance !== undefined);
        for (let value of this.additionalRoots) {
          // Populate old additionalRoots because we switched them out
          prevReVisit.add(value);
          this.visitValue(value);
        }
        for (let innerName of functionInfo.unbound) {
          let residualBinding = this.visitBinding(functionValue, innerName, false);
          if (residualBinding) {
            residualBinding.modified = true;
            funcInstance.residualFunctionBindings.set(innerName, residualBinding);
          }
        }
        this.additionalRoots = prevReVisit;
      }
    );
    this.inAdditionalFunction = oldInAdditionalFunction;
  }

  visitRoots(): void {
    let generator = this.realm.generator;
    invariant(generator);
    this.visitGenerator(generator);
    for (let moduleValue of this.modules.initializedModules.values()) this.visitValue(moduleValue);
    if (this.realm.react.enabled && this.shouldVisitReactLibrary) {
      this._visitReactLibrary();
    }

    // Do a fixpoint over all pure generator entries to make sure that we visit
    // arguments of only BodyEntries that are required by some other residual value
    let oldDelayedEntries = [];
    while (oldDelayedEntries.length !== this.delayedVisitGeneratorEntries.length) {
      oldDelayedEntries = this.delayedVisitGeneratorEntries;
      this.delayedVisitGeneratorEntries = [];
      for (let { commonScope, generator: entryGenerator, entry } of oldDelayedEntries) {
        this.commonScope = commonScope;
        this._withScope(entryGenerator, () => {
          entryGenerator.visitEntry(entry, this.createGeneratorVisitCallbacks(entryGenerator, commonScope));
        });
      }
    }

    // Artificially add additionalRoots to generators so that they can get serialized in parent scopes of additionalFunctions
    // if necessary.
    for (let value of this.additionalRoots) {
      let scopes = this.values.get(value);
      invariant(scopes);
      scopes = [...scopes];
      invariant(scopes.length > 0);
      invariant(scopes[0]);
      const firstGenerator = scopes[0] instanceof Generator ? scopes[0] : scopes[0].getParent();
      let commonAncestor = scopes.reduce((x, y) => commonAncestorOf(x, y), firstGenerator);
      invariant(commonAncestor instanceof Generator); // every scope is either the root, or a descendant
      commonAncestor.appendRoots([value]);
    }
  }

  _visitReactLibrary() {
    // find and visit the React library
    let reactLibraryObject = this.realm.react.reactLibraryObject;
    if (this.realm.react.output === "jsx") {
      // React might not be defined in scope, i.e. another library is using JSX
      // we don't throw an error as we should support JSX stand-alone
      if (reactLibraryObject !== undefined) {
        this.visitValue(reactLibraryObject);
      }
    } else if (this.realm.react.output === "create-element") {
      function throwError() {
        throw new FatalError("unable to visit createElement due to React not being referenced in scope");
      }
      // createElement output needs React in scope
      if (reactLibraryObject === undefined) {
        throwError();
      }
      invariant(reactLibraryObject instanceof ObjectValue);
      let createElement = reactLibraryObject.properties.get("createElement");
      if (createElement === undefined || createElement.descriptor === undefined) {
        throwError();
      }
      let reactCreateElement = Get(this.realm, reactLibraryObject, "createElement");
      this.visitValue(reactCreateElement);
    }
  }
}
