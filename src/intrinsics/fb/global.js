/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow strict-local */

import type { Realm } from "../../realm.js";
import { ArrayValue, ObjectValue } from "../../values/index.js";
import { createFbMocks } from "./fb-mocks.js";
import { createDefaultPropsHelper } from "../../react/utils.js";

export default function(realm: Realm): void {
  let global = realm.$GlobalObject;

  if (realm.react.enabled) {
    // Create it eagerly so it's created outside effect branches
    realm.react.defaultPropsHelper = createDefaultPropsHelper(realm);
    let emptyArray = new ArrayValue(realm);
    emptyArray.makeFinal();
    realm.react.emptyArray = emptyArray;
    let emptyObject = new ObjectValue(realm, realm.intrinsics.ObjectPrototype);
    emptyObject.makeFinal();
    realm.react.emptyObject = emptyObject;
  }

  if (realm.isCompatibleWith("fb")) {
    createFbMocks(realm, global);
  }
}
