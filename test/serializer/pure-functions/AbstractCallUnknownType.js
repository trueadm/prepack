// additional functions
// abstract effects

let obj = global.__abstract ? __abstract('object', '({foo: function() { return 1; }})') : {foo: function() { return 1; }};
if (global.__makeSimple) {
  __makeSimple(obj);
}
let condition = global.__abstract ? __abstract('boolean', 'true') : true;

function additional1() {
  return obj.foo();
}

function additional2() {
  function fn() {
    return 5;
  }
  let fnOrString = condition ? fn : 'string';
  return fnOrString();
}

inspect = function() {
  let ret1 = additional1();
  let ret2 = additional2();
  return ret1 + ret2;
}
