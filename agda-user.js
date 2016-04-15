var ag = require('./jAgda.LambdaMaps')
var nat = ag["ℕ"];
var z = nat.zero;
var s = nat.suc;

var three = s(s(s(z)));

function mk_nat(x) {
  var rv = nat.zero;
  for (var i = 0; i < x; i++) {
    rv = nat.suc(rv);
  }
  return rv;
}

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

// console.log(JSON.stringify(cvt_json(ag.Foo["example1"])));
// console.log(JSON.stringify(cvt_json(ag.Foo["example2"])));

function ap(lt, rt) {
  return {tp: "app", lt: lt, rt: rt};
}

function vr(n) {
  return {tp: "var", n: n};
}

function mk_term(t) {
  if (t.tp == "app")
    return ag.BareTerm.bapp(mk_term(t.lt), mk_term(t.rt));
  if (t.tp == "var")
    return ag.BareTerm.bhead(mk_nat(t.n));
}

var bare = mk_term(ap(vr(0), vr(0)));
console.log(cvt_json(ag.json_of_bare(bar)));
