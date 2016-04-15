var ag = require('./LambdaMaps-agda')
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

function cvt_bare(x) {
  return x({
    "bhead": function(x) { return cvt_nat(x) },
    "bapp" : function(x1, x2) { return cvt_bare(x1) + "(" + cvt_bare(x2) + ")"},
  });
}

function ap(lt, rt) {
  return {type: "app", L: lt, R: rt};
}

function vr(n) {
  return {type: "var", db: n};
}

function mk_term(t) {
  if (t.type == "app") {
    return ag.BareTerm.bapp(mk_term(t.L))(mk_term(t.R));
  }
  if (t.type == "var")
    return ag.BareTerm.bhead(mk_nat(t.db));
}

function go() {
  var bare = ap(vr(0), ap(vr(0), ap(vr(2), vr(0))));
  console.log(cvt_json(ag.json_of_bare(mk_term(bare))));
}

module.exports.map_of_term = function(bare) {
  return cvt_json(ag.json_of_bare(mk_term(bare)));
}
