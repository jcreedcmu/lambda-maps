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
		rv.push({type: "app", L: x1, R: x2});
	 });
  });
  return rv;
}


// atomic terms
// n = # lambdas, k = # free vars
function c_atom(n, k) {
  if (n < 0) return [];

  if (n == 0 && k == 1) {
	 return [{type: "var", subtype: "atom"}];
  }
  var rv = [];
  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {

		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		var ex = prod(cc_atom(a, b), cc_norm(n - a, k - b)).map(function(x) { x.subtype = "atom"; return x;});
		rv = rv.concat( ex );
	 }
  }
  return rv;
}

// normal terms
// n = # lambdas, k = # free vars
function c_norm(n, k) {
  if (n < 0) return [];

  return cc_atom(n,k).concat(cc_norm(n-1, k+1 , true).map(function(x) { return {type: "lam", B: x} }));

}

// vertic terms
// n = # lambdas, k = # free vertic vars, e = # free edge vars
function c_vert(n, k, e) {
  if (n < 0) return [];
  if (k == 0) e = false;

  if (n == 0 && k == 1 && !e) {
	 return [{type: "var"}];
  }
  var rv = cc_edge(n - 1, k + 1, e).map(function(x) { return {type: "lam", B: x} });

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
	 return [{type: "var", subtype: "edge"}];
  }
  var rv = cc_vert(n - 1, k + 1, e).map(function(x) { return {type: "lam", subtype: "edge", B:x} });
  for (var a = 0; a <= n; a++) {
	 for (var b = 0; b <= k; b++) {

		if (a == 0 && b == 0) continue;
		if (a == n && b == k) continue;
		rv = rv.concat( prod(cc_vert(a, b, e), cc_vert(n - a, k - b, b == 0 ? e :  false)) )
		  .map(function(x) { x.subtype = "edge"; return x});

	 }
  }
  return rv;
}

function c_struct(n, k) {
  if (n < 0) return [];
  if (k < 0) return [];

  var nn = n-1;
  var rv = cc_edge(nn, k+1 , true).map(function(x) { return {type: "lam", B:x} });


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
  if (x.type == "var") return "x"
  if (x.type == "lam") return "/" + string(x.B);

  if (x.type == "app") {
	 var head = x.L.type == "lam" ? "(" + string(x.L) + ")" : string(x.L);
	 var arg = x.R.type == "var" ? string(x.R) : "(" + string(x.R) + ")" ;
	 return head + " " + arg
  }
}

function estring(x) {
  if (x.type == "var") return "x"
  if (x.type == "lam") {
	 var bind = "/";
	 if (x.subtype == "edge") {
		bind = "!";
	 }
	 return bind + estring(x.B)
  }
  if (x.type == "app") {
	 var app = " ";
	 if (x.subtype == "edge") { app = "*" }
	 var head = x.L.type == "lam" ? "(" + estring(x.L) + ")" : estring(x.L);
	 var arg = x.R.type == "var" ? estring(x.R) : "(" + estring(x.R) + ")" ;
	 return head + app + arg
  }
}

function nstring(x) {
  if (x.type == "var") return "x"
  if (x.type == "lam") {
	 var bind = "/";
	 if (x.B.subtype == "atom") {
		bind = "!";
	 }
	 return bind + nstring(x.B)
  }
  if (x.type == "app") {
	 var app = " ";
	 if (x.R.subtype == "atom") { app = "*" }
	 var head = x.L.type == "lam" ? "(" + estring(x.L) + ")" : nstring(x.L);
	 var arg = x.R.type == "var" ? nstring(x.R) : "(" + nstring(x.R) + ")" ;
	 return head + app + arg
  }
}


function consec(x, lam) {
  if (x.type == "var") return 0;
  if (x.type == "lam") return (lam ? 1 : 0) + consec(x.B, true);
  if (x.type == "app") return consec(x.L, false) + consec(x.R, false);
}

function ids(x) {
  if (x.type == "var") return 0;
  if (x.type == "lam")  return x.B.type == "var" ? 1 : ids(x.B);
  if (x.type == "app") return ids(x.L) + ids(x.R);
}

function graphviz(prefix, x) {
  var rv = "";
  if (x.type == "lam") {
	 rv += graphviz("B" + prefix, x.B);
	 rv += prefix + " -> B" + prefix + "\n";
	 rv += prefix + "[color=\"0.4 0.8 0\"]\n";
  }
  if (x.type == "app") {
	 rv += graphviz("L" + prefix, x.L);
	 rv += graphviz("R" + prefix, x.R);
	 rv += prefix + " -> L" + prefix + "\n";
	 rv += prefix + " -> R" + prefix + "\n";
	 rv += prefix + "[color=\"0.4 0.8 0.6\"]\n";
  }

  return rv;
}

function census(s) {
  var a = 0, b = 0;
  for (var i = 0; i < s.length; i++) {
	 var x = s[i];
	 if (x == "/") a++;
	 if (x == "!") b++;
  }
  return a + "," + b;
}

function graphviz_list(x) {
  var rv = "digraph { \n";
  rv += "ranksep=0.2\n";
  rv += "node[nodesep=0.1,shape=circle,label=\"\",style=filled,color=\"0 0.5 0.8\",fixedsize=shape,width=0.1,height=0.1];\n"
  rv += "edge[penwidth=3,arrowsize=0,nodesep=0.1,color=\"0.7 0.1 0.9\"]\n";
  for(var i = 0; i < x.length; i++) {
	 rv += "subgraph{\n";
	 rv += graphviz(i, x[i]);
	 rv += "}\n";
  }
  rv += "}\n";
  return rv;
}
//console.log(cc_vert(2,1,false).map(string));
//console.log(cc_norm(3,0).map(string));


var t1 = cc_norm(7, 0).map(nstring).map(census).sort().join("-");
var t2 = cc_edge(7, 0).map(estring).map(census).sort().join("-");
console.log(t1 == t2);

// for(var i = 0; i < 7; i++) {
//   console.log(cc_edge(i,2,false).length);
// }

// subj.forEach(function(x) {
//   console.log(string(x));
// });
// console.log(subj.length);
