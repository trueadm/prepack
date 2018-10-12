/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

import { ObjectValue } from "../../values/index.js";
import { createReact } from "./react.js";
import { createReactDOM } from "./react-dom.js";
import { createReactNative } from "./react-native.js";
import { createReactRelay } from "./relay.js";
import { Get } from "../../methods/index.js";
import invariant from "../../invariant.js";

export default function(realm: Realm) {
  return {
    loadInternalReact: (name: string) => {
      return createReact(realm, name);
    },
    loadInternalReactDOM: (name: string) => {
      return createReactDOM(realm, name);
    },
    loadInternalReactNative: (name: string) => {
      return createReactNative(realm, name);
    },
    loadInternalPropTypes: (name: string) => {
      let react = realm.moduleResolver.import("react");
      invariant(react instanceof ObjectValue);
      let propTypes = Get(realm, realm.fbLibraries.react, "PropTypes");
      invariant(propTypes instanceof ObjectValue);
      return propTypes;
    },
    loadInternalReactRelay: (name: string) => {
      return createReactRelay(realm, name);
    },
  };
}
