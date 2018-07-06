// Copies of _7:3
// _7 is the variable for Object.assign. See DeadObjectAssign4.js for
// a larger explanation.

function f(x, foo) {
  var a = Object.assign({}, foo);
  var b = Object.assign({}, a);
  // b gets visited
  var someVal = b;
  if (x) {
    // a gets visited
    function foo() {
      return a;
    }
    someVal = foo;
  }
  // a should still exist
  return someVal;
}

if (global.__optimize) __optimize(f);

global.inspect = function() { return JSON.stringify(f(false, {a: 3})); }
