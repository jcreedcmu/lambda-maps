var ag = require('./jAgda.LambdaMaps')
var nat = ag["ℕ"];
var z = nat.zero;
var s = nat.suc;

var three = s(s(s(z)));

function make_nat(x) {
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

console.log(JSON.stringify(cvt_json(ag.Foo["example1"])));
console.log(JSON.stringify(cvt_json(ag.Foo["example2"])));

function ap(lt, rt) {
  return {tp: "app", lt: lt, rt: rt};
}

function vr(n) {
  return {tp: "var", n: n};
}

// n is an agda ℕ
// m is a javascript integer
function mk_choice(n, m) {
  var jn = cvt_nat(n);
  return "what"
}

function mk_term(t) {
  function aux(t, n) {
    if (t.tp == "app")
      return ag.RawTerm.rapp(n, aux(t.lt, n), aux(t.rt, nat.suc(n)));
    if (t.tp == "var")
      return ag.RawTerm.rhead(n, mk_choice(n, t.n));
  }
  return aux(t, make_nat(1));
}

console.log(cvt_nat(make_nat(5)));
