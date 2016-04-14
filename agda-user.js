var ag = require('./jAgda.LambdaMaps')
var nat = ag["ℕ"];
var z = nat.zero;
var s = nat.suc;

var three = s(s(s(z)));

function cvt(x) {
  return x({
    "zero": function() { return 0 },
    "suc" : function(x) { return cvt(x) + 1 }
  });
}
console.log(cvt(three));
