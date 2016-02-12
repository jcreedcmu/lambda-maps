function fact(a) {
  if (a <= 1) return 1;
  return fact(a-1) * a;
}
function choose(a, b) {
  return fact(a) / fact(b) / fact(a - b);
}
function memoize3(c) {
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
function memoize2(c) {
  var cache = {};
  function cc(n, k) {
	 var ky = n+","+k;
	 if (cache[ky] == null) {
		cache[ky] = c(n, k);
	 }
	 return cache[ky];
  }
  return cc;
}
var cc_norm = memoize2(c_norm);
var cc_atom = memoize2(c_atom);
var cc_vert = memoize3(c_vert);
var cc_edge = memoize3(c_edge);
var cc_struct = memoize3(c_struct);

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
// n = # lambdas, k = # free vars
function c_atom(n, k) {
  if (n < 0) return [];

  if (n == 0 && k == 1) {
	 return [["var"]];
  }
  var rv = [];
  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {

		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		var ex = prod(cc_atom(a, b), cc_norm(n - a, k - b));
		rv = rv.concat( ex );
	 }
  }
  return rv;
}

// normal terms
// n = # lambdas, k = # free vars
function c_norm(n, k) {
  if (n < 0) return [];

  return cc_atom(n,k).concat(cc_norm(n-1, k+1 , true).map(function(x) { return ["lam", x] }));

}

// vertic terms
// n = # lambdas, k = # free vertic vars, e = # free edge vars
function c_vert(n, k, e) {
  if (n < 0) return [];
  if (k == 0) e = false;

  if (n == 0 && k == 1 && !e) {
	 return [["var"]];
  }
  var rv = cc_edge(n - 1, k + 1, e).map(function(x) { return ["lam", x] });

  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {

		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		var ex = prod(cc_edge(a, b, e), cc_vert(n - a, k - b, b == 0 ? e : false));

		rv = rv.concat( ex );

	 }
  }

  return rv;
}

function c_edge(n, k, e) {
  if (n < 0) return [];
  if (k == 0) e = false;

  if (n == 0 && k == 1 && e) {
	 return [["var"]];
  }
  var rv = cc_vert(n - 1, k + 1, e).map(function(x) { return ["lam", x] });
  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {

		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		rv = rv.concat( prod(cc_vert(a, b, e), cc_vert(n - a, k - b, b == 0 ? e :  false)) );

	 }
  }
  return rv;
}

function c_struct(n, k) {
  if (n < 0) return [];
  if (k < 0) return [];

  var nn = n-1;
  var rv = cc_edge(nn, k+1 , true).map(function(x) { return ["lam", x] });


  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {
		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		rv = rv.concat( prod(cc_edge(a, b, false), cc_edge(n - a, k - b, false)) );
	 }

  }
  return rv;
}

function string(x) {
  if (x[0] == "var") return "x"
  if (x[0] == "lam") return "(/" + string(x[1]) + ")"
  if (x[0] == "app") return "(" + string(x[1]) + " " + string(x[2]) + ")"
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


//console.log(cc_edge(1,0,false).map(string));
//console.log(cc_vert(3,1).map(string));


for(var i = 0; i < 7; i++) {
  console.log(cc_norm(i,0).length);
}

// subj.forEach(function(x) {
//   console.log(string(x));
// });
// console.log(subj.length);
