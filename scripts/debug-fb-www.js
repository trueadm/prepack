/**
 * Copyright (c) 2017-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/* @flow */

// NOTE:
// put the input fb-www file in ${root}/fb-www/input.js
// the compiled file will be saved to ${root}/fb-www/output.js

let prepackSources = require("../lib/prepack-node.js").prepackSources;
let path = require("path");
let { readFile, writeFile, existsSync } = require("fs");
let { promisify } = require("util");
let readFileAsync = promisify(readFile);
let writeFileAsync = promisify(writeFile);
let chalk = require("chalk");
let { Linter } = require("eslint");

let errorsCaptured = [];

function printError(error) {
  let msg = `${error.errorCode}: ${error.message}`;
  if (error.location) {
    let loc_start = error.location.start;
    let loc_end = error.location.end;
    msg += ` at ${loc_start.line}:${loc_start.column} to ${loc_end.line}:${loc_end.column}`;
  }
  switch (error.severity) {
    case "Information":
      console.log(`Info: ${msg}`);
      return "Recover";
    case "Warning":
      console.warn(`Warn: ${msg}`);
      return "Recover";
    case "RecoverableError":
      console.error(`Error: ${msg}`);
      return "Fail";
    case "FatalError":
      console.error(`Fatal Error: ${msg}`);
      return "Fail";
    default:
      console.log(msg);
  }
}

let prepackOptions = {
  errorHandler: diag => {
    if (diag.severity === "Information") {
      console.log(diag.message);
      return "Recover";
    }
    errorsCaptured.push(diag);
    if (diag.severity !== "Warning") {
      if (diag.errorCode === "PP0025") {
        // recover from `unable to evaluate "key" and "ref" on a ReactElement due to an abstract config passed to createElement`
        return "Recover";
      }
      return "Fail";
    }
    return "Recover";
  },
  compatibility: "fb-www",
  internalDebug: true,
  serialize: true,
  uniqueSuffix: "",
  maxStackDepth: 100,
  reactEnabled: true,
  reactOutput: "jsx",
  reactVerbose: true,
  inlineExpressions: true,
  invariantLevel: 0,
  simpleClosures: true,
  abstractValueImpliesMax: 1000,
};
let inputPath = path.resolve("fb-www/input.js");
let outputPath = path.resolve("fb-www/output.js");
let componentsListPath = path.resolve("fb-www/components.txt");
let components = new Map();
let startTime = Date.now();
let uniqueEvaluatedComponents = 0;

function compileSource(source) {
  let serialized;
  try {
    serialized = prepackSources([{ filePath: inputPath, fileContents: source, sourceMapContents: "" }], prepackOptions);
  } catch (e) {
    console.log(`\n${chalk.inverse(`=== Diagnostics Log ===`)}\n`);
    errorsCaptured.forEach(error => printError(error));
    throw e;
  }
  return {
    stats: serialized.reactStatistics,
    code: serialized.code,
  };
}

async function readComponentsList() {
  if (existsSync(componentsListPath)) {
    let componentsList = await readFileAsync(componentsListPath, "utf8");
    let componentNames = componentsList.split("\n");

    for (let componentName of componentNames) {
      components.set(componentName, "missing");
    }
  }
}

function lintCompiledSource(source) {
  let linter = new Linter();
  let errors = linter.verify(source, {
    env: {
      commonjs: true,
      browser: true,
    },
    rules: { "no-undef": "error" },
    parserOptions: {
      ecmaVersion: 6,
      ecmaFeatures: {
        jsx: true,
      },
    },
    globals: {
      // FB
      React: true,
      Env: true,
      Bootloader: true,
      JSResource: true,
      babelHelpers: true,
      asset: true,
      cx: true,
      cssVar: true,
      csx: true,
      errorDesc: true,
      errorHelpCenterID: true,
      errorSummary: true,
      gkx: true,
      glyph: true,
      ifRequired: true,
      ix: true,
      fbglyph: true,
      fbt: true,
      requireWeak: true,
      xuiglyph: true,
      // ES 6
      Promise: true,
      Map: true,
      Set: true,
      Proxy: true,
      Symbol: true,
      WeakMap: true,
      // Vendor specific
      MSApp: true,
      __REACT_DEVTOOLS_GLOBAL_HOOK__: true,
      // CommonJS / Node
      process: true,
    },
  });
  if (errors.length > 0) {
    console.log(`\n${chalk.inverse(`=== Validation Failed ===`)}\n`);
    for (let error of errors) {
      console.log(`${chalk.red(error.message)} ${chalk.gray(`(${error.line}:${error.column})`)}`);
    }
    process.exit(1);
  }
}

async function compileFile() {
  let source = await readFileAsync(inputPath, "utf8");
  let { stats, code } = await compileSource(source);
  await writeFileAsync(outputPath, code);
  lintCompiledSource(code);
  // $FlowFixMe: no idea what this is about
  return stats;
}

function printReactEvaluationGraph(evaluatedRootNode, depth) {
  if (Array.isArray(evaluatedRootNode)) {
    for (let child of evaluatedRootNode) {
      printReactEvaluationGraph(child, depth);
    }
  } else {
    let status = evaluatedRootNode.status.toLowerCase();
    let message = evaluatedRootNode.message !== "" ? `: ${evaluatedRootNode.message}` : "";
    let name = evaluatedRootNode.name;
    let line;
    if (status === "inlined") {
      line = `${chalk.gray(`-`)} ${chalk.green(name)} ${chalk.gray(`(${status + message})`)}`;
    } else if (status === "unsupported_completion" || status === "unknown_type" || status === "bail-out") {
      line = `${chalk.gray(`-`)} ${chalk.red(name)} ${chalk.gray(`(${status + message})`)}`;
    } else {
      line = `${chalk.gray(`-`)} ${chalk.yellow(name)} ${chalk.gray(`(${status + message})`)}`;
    }
    if (components.has(name)) {
      let currentStatus = components.get(name);

      if (currentStatus === "missing") {
        uniqueEvaluatedComponents++;
        currentStatus = [currentStatus];
        components.set(name, currentStatus);
      } else if (Array.isArray(currentStatus)) {
        currentStatus.push(status);
      }
    }
    console.log(line.padStart(line.length + depth));
    printReactEvaluationGraph(evaluatedRootNode.children, depth + 2);
  }
}

readComponentsList()
  .then(compileFile)
  .then(result => {
    console.log(`\n${chalk.inverse(`=== Compilation Complete ===`)}\n`);
    console.log(chalk.bold(`Evaluated Tree:`));
    printReactEvaluationGraph(result.evaluatedRootNodes, 0);

    if (components.size > 0) {
      console.log(`\n${chalk.inverse(`=== Status ===`)}\n`);
      for (let [componentName, status] of components) {
        if (status === "missing") {
          console.log(`${chalk.red(`✖`)} ${componentName}`);
        } else {
          console.log(`${chalk.green(`✔`)} ${componentName}`);
        }
      }
    }

    console.log(`\n${chalk.inverse(`=== Summary ===`)}\n`);
    if (components.size > 0) {
      console.log(`${chalk.gray(`Optimized Components`)}: ${uniqueEvaluatedComponents}/${components.size}`);
    }
    console.log(`${chalk.gray(`Optimized Nodes`)}: ${result.componentsEvaluated}`);
    console.log(`${chalk.gray(`Inlined Nodes`)}: ${result.inlinedComponents}`);
    console.log(`${chalk.gray(`Optimized Trees`)}: ${result.optimizedTrees}`);
    console.log(`${chalk.gray(`Optimized Nested Closures`)}: ${result.optimizedNestedClosures}`);

    let timeTaken = Math.floor((Date.now() - startTime) / 1000);
    console.log(`${chalk.gray(`Compile time`)}: ${timeTaken}s\n`);
    // warning about ref and keys
    console.log(`Warning: the build assumes that ref and key aren't being spread.`);
  })
  .catch(e => {
    console.log(`\n${chalk.inverse(`=== Compilation Failed ===`)}\n`);
    console.error(e.nativeStack || e.stack);
    process.exit(1);
  });
