function initMockCommonJS(realm, { NativeFunctionValue, ObjectValue, PropertyDescriptor }) {
  let global = realm.$GlobalObject;
  let moduleMapObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);

  // apply a module map to the global
  global.$DefineOwnProperty(
    "moduleMap",
    new PropertyDescriptor({
      value: moduleMapObject,
      writable: true,
      enumerable: false,
      configurable: true,
    })
  );
  // apply require mock function to global
  global.$DefineOwnProperty(
    "require",
    new PropertyDescriptor({
      value: new NativeFunctionValue(realm, "require", "require", 0, (context, [requireNameVal]) => {
        let result = realm.moduleResolver.import(requireNameVal.value);
        if (typeof result === "string") {
          invariant(false, "TODO load paths from file system");
        } else if (result === Symbol.for("resolve module at runtime")) {
          invariant(false, "TODO make an abstract require value");
        }
        return result;
      }),
      writable: true,
      enumerable: false,
      configurable: true,
    })
  );
}

module.exports = function(realm, { transformModuleValue, transformModuleSource }, objects) {
  let react;
  let reactDOM;
  let reactDOMServer;
  let reactNative;
  let propTypes;
  let reactRelay;

  initMockCommonJS(realm, objects);

  transformModuleSource((name, source) => {
    // Given we're make a mock basic CommonJS system we need to wrap each
    // module in a wrapper with require, modules and exports.
    return `const module = { exports: {} }; global.moduleMap["${name}"] = module;\n(function(require, exports, module){\n${source}\n})(global.require, module.exports, module);`;
  });

  transformModuleValue((name, value) => {
    if (name === "[Entry]") {
      let { ObjectValue } = objects;
      let global = realm.$GlobalObject;
      let moduleMapObject = global.properties.get("moduleMap").descriptor.value;
      let entryModules = moduleMapObject.properties.get("[Entry]").descriptor.value;
      let entryModulesExports = entryModules.properties.get("exports").descriptor.value;
      // Output the value of the entry value
      realm.generator.emitModuleExportsAssignment(entryModulesExports);
    }
    return value;
  });

  return function resolveModuleName(name, resolveAtRuntime, internalModules) {
    switch (name) {
      case "react":
        if (!react) react = internalModules.loadInternalReact("react");
        return react;
      case "react-dom":
        if (!reactDOM) reactDOM = internalModules.loadInternalReactDOM("react-dom");
        return reactDOM;
      case "react-dom/server":
        if (!reactDOMServer) reactDOMServer = internalModules.loadInternalReact("react-dom/server");
        return reactDOMServer;
      case "react-native":
        if (!reactNative) reactNative = internalModules.loadInternalReactNative("react-native");
        return reactNative;
      case "prop-types":
        if (!propTypes) propTypes = internalModules.loadInternalPropTypes("prop-types");
        return propTypes;
      case "react-relay":
        if (!reactRelay) reactRelay = internalModules.loadInternalReactRelay("react-relay");
        return reactRelay;
      default:
        return resolveAtRuntime;
    }
  };
};
