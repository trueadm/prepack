var React = require("React");
// the JSX transform converts to React, so we need to add it back in
this["React"] = React;

if (!this.__safeSideEffect) {
  __safeSideEffect = x => x();
}

if (!this.__evaluatePureFunction) {
  this.__evaluatePureFunction = function(f) {
    return f();
  };
}

__evaluatePureFunction(function() {
  function FbtResult() {}
  FbtResult.prototype.$$typeof = Symbol.for("react.element");

  function fbt() {}
  function param() {}
  function plural(shouldThrow) {
    if (shouldThrow) {
      __safeSideEffect(function() {
        throw new Error("no");
      });
    }
  }

  var React = require("react");

  function App(props) {
    return React.createElement(
      "div",
      new FbtResult({}, [param(props.foo), plural(props.bar)])
    );
  }

  App.getTrials = function(renderer, Root) {
    renderer.update(<Root bar={false} />);
    return [["fb19 mocks", renderer.toJSON()]];
  };

  if (this.__optimizeReactComponentTree) {
    __optimizeReactComponentTree(App, {
      firstRenderOnly: true
    });
  }

  module.exports = App;
});
