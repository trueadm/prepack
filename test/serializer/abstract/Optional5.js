// add at runtime: let x = { items: "abc" };
let x = { items: "abc" };
let y = global.__abstract ? __abstract(x, "x") : x;

function getCollectionData(collection) {
  return {
    filter: true,
    collection: collection != null && collection.items,
  };
}

z = getCollectionData(y);

inspect = function() { return JSON.stringify(z); }
