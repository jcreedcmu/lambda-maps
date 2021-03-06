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

module.exports.c_vert = c_vert;
module.exports.c_edge = c_edge;

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

function gen_trif() {
  var trif = {};

  function gen(thisname, varname, leftf, rightf) {
	 return function (n, G) {
		if (n < 0) return [];
		if (n == 0 && G == thisname)
		  return [{type: "var"}];
		var rv = trif[leftf](n-1, G+varname).map(function(x) { return {type: "lam", B:x} });
		for (var a = 0; a <= n; a++) {
		  for (var b = 0; b <= G.length; b++) {
			 if (a == 0 && b == 0) continue;
			 if (a == n && b == G.length) continue;
			 rv = rv.concat(prod(trif[leftf](a, G.substring(0,b)),
										trif[rightf](n - a, G.substring(b,G.length))));
		  }

		}
		return rv;
	 }
  }
  trif["v"] = memoize2(gen("v", "s", "e", "v"));
  trif["e"] = memoize2(gen("e", "v", "v", "s"));
  trif["s"] = memoize2(gen("s", "e", "s", "e"));
  return trif;
}

function gen_bif() {
  var bif = {};

  function gen(thisname, varname, body, leftf, rightf) {
	 return function (n, G) {
		if (n < 0) return [];
		if (n == 0 && G == thisname)
		  return [{type: "var"}];
		var rv = bif[body](n-1, varname(G)).map(function(x) { return {type: "lam", B:x} });
		if (leftf != null) {
		  for (var a = 0; a <= n; a++) {
			 for (var b = 0; b <= G.length; b++) {
				if (a == 0 && b == 0) continue;
				if (a == n && b == G.length) continue;
				rv = rv.concat(prod(bif[leftf](a, G.substring(0,b)),
										  bif[rightf](n - a, G.substring(b,G.length))));
			 }
		  }
		}
		return rv;
	 }
  }
  bif["v"] = memoize2(gen("v", function(G) { return "e"+G }, "v", "e", "v" ));
  bif["e"] = memoize2(gen("e", function(G) { return  G+"v"}, "v" ));
  return bif;
}


function lstring(s) {
  return traverse(s, {
	 vor: function(x) { return "x" },
	 lam: function(B, x) { return "/" + B; },
	 app: function(L, R, x) {
		var head = x.L.type == "lam" ? "(" + L + ")" : L;
		var arg = x.R.type == "var" ? R : "(" + R + ")" ;
		return head + " " + arg
	 }});
}

function estring(s) {
  return traverse(s, {
	 vor: function(x) { return "x" },
	 lam: function(B, x) {
		var bind = "/";
		if (x.subtype == "edge") bind = "!";
		return bind + B;
	 },
	 app: function(L, R, x) {
		var app = " ";
		if (x.subtype == "edge") app = "*";
		var head = x.L.type == "lam" ? "(" + L + ")" : L;
		var arg = x.R.type == "var" ? R : "(" + R + ")" ;
		return head + app + arg
	 }});
}


function traverse(s, f) {
  if (s.type == "var") { return f.vor(s, s.db); }
  if (s.type == "lam") { return f.lam(traverse(s.B, f), s) }
  if (s.type == "app") { return f.app(traverse(s.L, f), traverse(s.R, f), s); }
}

module.exports.traverse = traverse;

function nstring(s) {
  return traverse(s, {
	 vor: function(x) { return "x" },
	 lam: function(B, x) {
		var bind = "/";
		if (x.B.subtype == "atom") bind = "!";
		return bind + B;
	 },
	 app: function(L, R, x) {
		var app = " ";
		if (x.R.subtype == "atom") app = "*";
		var head = x.L.type == "lam" ? "(" + L + ")" : L;
		var arg = x.R.type == "var" ? R : "(" + R + ")" ;
		return head + app + arg
	 }});
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


function tally(es) {
  var counts = {};
  for(var i = 0; i < es.length; i++) {
	 counts[es[i]] = 1 + (counts[es[i]] || 0);
  }
  return counts;
}

function viol(s) {
  return traverse(s, {
	 vor: function(x) { return false; },
	 lam: function(B, x) {
		return B || (x.subtype != "edge" && x.B.type == "lam" && x.B.subtype == "edge");
	 },
	 app: function(L, R, x) {
		return L || R;
	 },
  });
}

// XXX I am modifying this function to double-count elams, to test whether that counts
// locally orientable rooted maps
function vertex_and_edge_terminal() {
  function count_v(l, v) {
	 var rv = 0;
	 if (l == 0 && v == 0) return 1;
	 //console.log("l v ?", l, v);
	 for (var i = 0; i <= l; i++) {
		for (var j = 0; j <= v; j++) {
		  if (i == 0 && j == 0)  continue;
		  //console.log("i j I J", i, j, l-i, v-j);
		  rv += count_e(i, j) * count_v(l-i, v-j) * choose(v, j);
		}
	 }
	 if (l >= 1)
		rv += count_v(l-1,v+1);
	 return rv;
  }

  function count_e(l, v) {
	 var rv = 0;
	 if (l == 0 && v == 1) return 1;
	 rv += 2 * count_v(l-1,v);
	 return rv;
  }
  return count_e;
}

module.exports.vertex_and_edge_terminal = vertex_and_edge_terminal();

function linear_subset() {
  function count_atom(l, v) {
	 var rv = 0;
	 if (l == 0 && v == 1) return 1;
	 for (var i = 0; i <= l; i++) {
		for (var j = 0; j <= v; j++) {
		  if (i == 0 && j == 0)  continue;
		  if (i == l && j == v)  continue;
		  rv += count_subnorm(i, j) * count_atom(l-i, v-j) * choose(v, j);
		}
	 }
	 return rv;
  }

  function count_spine(l, v) {
	 var rv = 0;
	 if (l == 0 && v == 0) return 1;
	 for (var i = 0; i <= l; i++) {
		for (var j = 0; j <= v; j++) {
		  if (i == 0 && j == 0)  continue;
		  rv += count_subnorm(i, j) * count_spine(l-i, v-j) * choose(v, j);
		}
	 }
	 return rv;
  }

  function count_subnorm(l, v) {
	 var rv = count_atom(l,v);
	 if (l >= 1) {
		rv += count_norm(l-1,v+1);
		rv += count_spine(l-1,v);
	 }
	 return rv;
  }

  function count_norm(l, v) {
	 var rv = 0;
	 if (l >= 1) {
		rv += count_norm(l-1,v+1);
		rv += count_spine(l-1,v);
	 }
	 return rv;
  }

  return {a:count_atom,s:count_spine,n:count_norm,x:count_subnorm};
}


// enumerating atomic linear terms in local-exchange-quotient representation
// R ::= x | R (\x.R)
// n = # applications, k = # free vars
var cc_le_atom = memoize2(c_le_atom);
function c_le_atom(n, k) {
  var rv = [];
  if (n < 0) return rv;
  if (n == 0) {
    for (var i = 0; i < k; i++) {
      rv.push({type: "var", db: i});
    }
    return rv;
  }

  for (var a = 0; a < n; a++) {
	 var ex = prod(cc_le_atom(a, k), cc_le_atom(n - 1 - a, k + 1));
	 rv = rv.concat( ex );
  }
  return rv;
}

module.exports.c_le_atom = cc_le_atom;
