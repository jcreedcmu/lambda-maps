// computes A258222

function prod(l1, l2) {
  rv = [];
  l1.forEach(function (x1) {
	 l2.forEach(function (x2) {
		rv.push("(" + x1 + ")" + x2);
	 });
  });
  return rv;
}
function sum(xs) {
  var s = 0;
  for (var i = 0; i < xs.length; i++)
	 s += xs[i];
  return s;
}
function memoize1(c) {
  var cache = {};
  function cc(n) {
	 var ky = n;
	 if (cache[ky] == null) {
		cache[ky] = c(n);
	 }
	 return cache[ky];
  }
  return cc;
}

function dyck(n) {
  if (n == 0) { return [""] }
  var rv = [];
  for (var i = 0; i < n; i++) {
	 rv = rv.concat(prod(cdyck(i), cdyck(n-i-1)));
  }
  return rv;
}
cdyck = memoize1(dyck);

function evaluate(k) {
  return function (path) {
	 var x = 0;
	 var y = 0;
	 var prod = 1;
	 for (var i = 0; i < path.length; i++) {
		if (path[i] == ")" && path[i-1] == "(") {
		  prod *= (k * x + y) / y;
		}
		x++;
		y += path[i] == "(" ? 1 : -1;
	 }
	 return prod;
  }
}

for (var j = 0; j < 8; j++) {
  var ds = dyck(j);
  var out = "";
  for (var i = 0; i < 10; i++) {
	 out += Math.round(  sum(ds.map(evaluate(i)))) + "\t";
  }
  console.log(out);
}
