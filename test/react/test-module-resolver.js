function initMockCommonJS(realm, { NativeFunctionValue, PropertyDescriptor }) {
  let global = realm.$GlobalObject;

   // apply require() mock
   global.$DefineOwnProperty(
    "require",
    new PropertyDescriptor({
      value: new NativeFunctionValue(realm, "require", "require", 0, (context, [requireNameVal]) => {
        return realm.moduleResolver.import(requireNameVal.value);
      }),
      writable: true,
      enumerable: false,
      configurable: true,
    })
   );
}

module.exports = function(realm, objects) {
  let react;
  let reactDOM;
  let reactDOMServer;
  let reactNative;
  let propTypes;
  let reactRelay;

  initMockCommonJS(realm, objects);

  return function resolveModuleName(name, resolveAtRuntime, internalModules) {
    switch (name) {
      case "react":
        if (!react) react = internalModules.loadInternalReact("react");
        return react;
      case "react-dom":
        if (!reactDOM) reactDOM = internalModules.loadInternalReact("react-dom");
        return reactDOM;
      case "react-dom/server":
        if (!reactDOMServer) reactDOMServer = internalModules.loadInternalReact("react-dom/server");
        return reactDOMServer;
      case "react-native":
        if (!reactNative) reactNative = internalModules.loadInternalReact("react-native");
        return reactNative;
      case "prop-types":
        if (!propTypes) propTypes = internalModules.loadInternalReact("prop-types");
        return propTypes;
      case "react-relay":
        if (!reactRelay) reactRelay = internalModules.loadInternalReact("react-relay");
        return reactRelay;
      default:
        return resolveAtRuntime;
    }
  };
};
