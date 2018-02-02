/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import type { Realm } from "../../realm.js";
import { parseExpression } from "babylon";
import { ObjectValue } from "../../values/index.js";
import { Environment } from "../../singletons.js";
import { ECMAScriptSourceFunctionValue } from "../../values/index.js";
import invariant from "../../invariant";

let reactRelayCode = `
  function createReactRelay(RelayRuntime, React) {
    var {RelayProfiler} = RelayRuntime;

    class ReactRelayQueryRenderer extends React.Component {

    }

    var containerContextTypes = {
      relay: null,
    };

    function mapObject(object, fn, ctx) {
      var result = []
      Object.keys(object).forEach(function (value, key) {
        result.push(fn.call(ctx, value, key, object))
      })
      return result
    }

    function isReactComponent(component) {
      return !!(
        component &&
        typeof component.prototype === 'object' &&
        component.prototype &&
        component.prototype.isReactComponent
      );
    }

    function getReactComponent(Component) {
      if (isReactComponent(Component)) {
        return Component;
      } else {
        return null;
      }
    }

    function getComponentName(Component) {
      let name;
      var ComponentClass = getReactComponent(Component);
      if (ComponentClass) {
        name = ComponentClass.displayName || ComponentClass.name;
      } else if (typeof Component === 'function') {
        // This is a stateless functional component.
        name = Component.displayName || Component.name || 'StatelessComponent';
      } else {
        name = 'ReactElement';
      }
      return String(name);
    }

    function getContainerName(Component) {
      return 'Relay(' + getComponentName(Component) + ')';
    }

    function createFragmentContainerWithFragments(Component, fragments) {
      var ComponentClass = getReactComponent(Component);
      var componentName = getComponentName(Component);
      var containerName = \`Relay(\${componentName})\`;
    
      class Container extends React.Component {
        constructor(props, context) {
          super(props, context);
          var relay = context.relay;

          this._handleFragmentDataUpdate = () => {
            var data = this._resolver.resolve();
            var profiler = RelayProfiler.profile(
              'ReactRelayFragmentContainer.handleFragmentDataUpdate',
            );
            this.setState(
              {
                data,
                relayProp: Object.assign({}, 
                  this.state.relayProp,
                  { isLoading: this._resolver.isLoading() },
                ),
              },
              profiler.stop,
            );
          };

          var {createFragmentSpecResolver} = relay.environment.unstable_internal;
          this._resolver = createFragmentSpecResolver(
            relay,
            containerName,
            fragments,
            props,
            this._handleFragmentDataUpdate
          );
          this.state = {
            data: this._resolver.resolve(),
            relayProp: {
              isLoading: this._resolver.isLoading(),
              environment: relay.environment,
            },
          };
        }

        render() {
          if (ComponentClass) {
            return (
              React.createElement(
                ComponentClass,
                Object.assign(
                  {},
                  this.props,
                  this.state.data,
                  {ref: this.props.componentRef || 'component'},
                  {relay: this.state.relayProp}
                )
              )
            );
          } else {
            // Stateless functional, doesn't support \`ref\`
            return React.createElement(
              Component,
              Object.assign(
                {},
                this.props,
                this.state.data,
                {relay: this.state.relayProp}
              )
            );
          }
        }
      }

      Container.contextTypes = containerContextTypes;
      Container.displayName = containerName;
    
      return Container;
    }

    function buildReactRelayContainer(
      ComponentClass,
      fragmentSpec,
      createContainerWithFragments
    ) {
      var containerName = getContainerName(ComponentClass);

      var environment;
      var Container;
      function ContainerConstructor(props, context) {
        if (Container == null || context.relay.environment !== environment) {
          environment = context.relay.environment;
          var {getFragment: getFragmentFromTag} = environment.unstable_internal;
          var fragments = mapObject(fragmentSpec, getFragmentFromTag);
          Container = createContainerWithFragments(ComponentClass, fragments);
        }

        return new Container(props, context);
      }
      ContainerConstructor.contextTypes = containerContextTypes;
      ContainerConstructor.displayName = containerName;

      return ContainerConstructor;
    }

    function createFragmentContainer(Component, fragmentSpec) {
      return buildReactRelayContainer(
        Component,
        fragmentSpec,
        createFragmentContainerWithFragments,
      );
    }

    var ReactRelayFragmentContainer = {
      createContainer: createFragmentContainer,
      createContainerWithFragments: createFragmentContainerWithFragments,
    };

    var ReactRelayPaginationContainer = {
      
    };

    var ReactRelayRefetchContainer = {

    };
    
    return {
      QueryRenderer: ReactRelayQueryRenderer,

      MutationTypes: RelayRuntime.MutationTypes,
      RangeOperations: RelayRuntime.RangeOperations,
    
      commitLocalUpdate: RelayRuntime.commitLocalUpdate,
      commitMutation: RelayRuntime.commitMutation,
      createFragmentContainer: ReactRelayFragmentContainer.createContainer,
      createPaginationContainer: ReactRelayPaginationContainer.createContainer,
      createRefetchContainer: ReactRelayRefetchContainer.createContainer,
      fetchQuery: RelayRuntime.fetchQuery,
      graphql: RelayRuntime.graphql,
      requestSubscription: RelayRuntime.requestSubscription,
    };
  }
`;
let reactRelayCodeAst = parseExpression(reactRelayCode, { plugins: ["flow"] });

export function createMockReactRelay(realm: Realm, relayRequireName: string): ObjectValue {
  let reactRelayFactory = Environment.GetValue(realm, realm.$GlobalEnv.evaluate(reactRelayCodeAst, false));
  invariant(reactRelayFactory instanceof ECMAScriptSourceFunctionValue);
  // if these errors happen, the environment hasn't been setup right, these should break stop the compiler
  // or the evaluation will be be wrong (React and Relay's internals are essential for ReactRelay)
  invariant(
    realm.fbLibraries.relayRuntime,
    "unable to load ReactRelay mock due to RelayRuntime not being referenced in scope"
  );
  invariant(realm.fbLibraries.react, "unable to load ReactRelay mock due to React not being referenced in scope");

  let factory = reactRelayFactory.$Call;
  invariant(factory !== undefined);
  let reactRelayValue = factory(realm.intrinsics.undefined, [realm.fbLibraries.relayRuntime, realm.fbLibraries.react]);
  reactRelayValue.intrinsicName = `require("${relayRequireName}")`;
  invariant(reactRelayValue instanceof ObjectValue);

  return reactRelayValue;
}
