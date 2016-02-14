function v(k, n, s) {
  if (k < 0) return 0;
  if (n < 0) return 0;
  if (s == 1 && k == 0 && n == 0) return 1;
  if (s <= 1) return 0;
  if (s % 2) {
	 return v(k+1, n-1, s-1) + v(k, n-1, 2*s-1) + v(k-1, n , (s - 1) / 2);
  }
  else {
	 return v(k+1, n-1, s+1) + v(k, n-1, 2*s + 3);
  }
}
function debug(k, n, s) {
  if (k < 0) return 0;
  if (n < 0) return 0;
  if (s == 1 && k == 0 && n == 0) return 1;
  if (s <= 1) return 0;
  if (s % 2) {
	 console.log([k+1, n-1, s-1],[k, n-1, 2*s-1],[k-1, n , (s - 1) / 2]);
  }
  else {
	 console.log([k+1, n-1, s+1], [k, n-1, 2*s + 3]);
  }
}
// for (var i = 0; i < 20; i++) {
//   show(0, i, 2);
// }
function show(a, b, c) {
  console.log([a, b, c, ":     ", v(a, b, c)].join(" "));
}
show(0,3,2);
show(0,2,7);
show(1,1,6);
show(2,0,7);
show(1,0,3);
show(0,0,1);

show(1,2,3);
show(2,1,2);
show(1,1,5);
show(0,2,1);
