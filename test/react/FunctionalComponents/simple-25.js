var React = require("react");

function Child() {
  return <div>This should be inlined</div>;
}

function App(props) {
  var a = props.x ? null : { foo: <Child /> };
  return a.foo;
}

App.getTrials = function(renderer, Root) {
  renderer.update(<Root />);
  return [["simple conditions #2", renderer.toJSON()]];
};

if (this.__optimizeReactComponentTree) {
  __optimizeReactComponentTree(App);
}

module.exports = App;
