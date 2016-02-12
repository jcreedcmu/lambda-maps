function fact(a) {
  if (a <= 1) return 1;
  return fact(a-1) * a;
}
function choose(a, b) {
  return fact(a) / fact(b) / fact(a - b);
}
function memoize(c) {
  var cache = {};
  function cc(n, k, e) {
	 var ky = n+","+k+","+e;
	 if (cache[ky] == null) {
		cache[ky] = c(n, k, e);
	 }
	 return cache[ky];
  }
  return cc;
}

var cc_atom = memoize(c_atom);
var cc_normal = memoize(c_normal);
var cc_struct = memoize(c_struct);

function prod(l1, l2) {
  rv = [];
  l1.forEach(function (x1) {
	 l2.forEach(function (x2) {
		rv.push(["app", x1, x2]);
	 });
  });
  return rv;
}

// atomic terms
// n = # lambdas, k = # free atomic vars, e = # free normal vars
function c_atom(n, k, e) {
  if (n < 0) return [];


  if (n == 0 && k == 1 && !e) {
	 return [["var"]];
  }
  var rv = cc_normal(n - 1, k + 1, e).map(function(x) { return ["lam", x] });
  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {

		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		  rv = rv.concat( prod(cc_normal(a, b, e), cc_atom(n - a, k - b, false)) );

	 }
  }
  return rv;
}

function c_normal(n, k, e) {
  if (n < 0) return [];


  if (n == 0 && k == 1 && e) {
	 return [["var"]];
  }
  var rv = cc_atom(n - 1, k + 1, e).map(function(x) { return ["lam", x] });
  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {

		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		  rv = rv.concat( prod(cc_atom(a, b, e), cc_atom(n - a, k - b, false)) );

	 }
  }
  return rv;
}

function c_struct(n, k) {
  if (n < 0) return [];
  if (k < 0) return [];


  var rv = cc_normal(n - 1, k , true).map(function(x) { return ["lam", x] });

  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {
		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		rv = rv.concat( prod(cc_normal(a, b, false), cc_normal(n - a, k - b, false)) );
	 }

  }
  return rv;
}

function string(x) {
  if (x[0] == "var") return "*"
  if (x[0] == "lam") return "/" + string(x[1])
  if (x[0] == "app") return "(" + string(x[1]) + "@" + string(x[2]) + ")"
}

function consec(x, lam) {
  if (x[0] == "var") return 0;
  if (x[0] == "lam") return (lam ? 1 : 0) + consec(x[1], true);
  if (x[0] == "app") return consec(x[1], false) + consec(x[2], false);
}

function ids(x) {
  if (x[0] == "var") return 0;
  if (x[0] == "lam")  return x[1][0] == "var" ? 1 : ids(x[1]);
  if (x[0] == "app") return ids(x[1]) + ids(x[2]);
}


subj = cc_normal(4,0,0);
subj.forEach(function(x) {
  console.log(string(x));
});
console.log(subj.length);
