var ag = require('./jAgda.LambdaMaps')
var nat = ag["ℕ"];
var z = nat.zero;
var s = nat.suc;

var three = s(s(s(z)));

function cvt_nat(x) {
  return x({
    "zero": function() { return 0 },
    "suc" : function(x) { return cvt_nat(x) + 1 },
  });
}

function cvt_list(x) {
  return x({
    "[]": function() { return [] },
    "_,_" : function(h, tl) { return [cvt_json(h)].concat(cvt_list(tl)) },
  });
}

function cvt_json(x) {
  return x({
    "jstr": function(x) { return x },
    "jnat" : function(x) { return cvt_nat(x) },
    "jarr" : function(x) { return cvt_list(x) },
  });
}

console.log(JSON.stringify(cvt_json(ag.Foo["example1"])));
console.log(JSON.stringify(cvt_json(ag.Foo["example2"])));
