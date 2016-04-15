var lam = require('./lambda-lib');
var agda = require('./agda-user');

// for (var i = 0; i < 10; i++) {
//   console.log(lam.c_le_atom(i, 1).length);
// }

function string_of_term(s) {
  return lam.traverse(s, {
	 vor: function(x, db) { return db },
	 app: function(L, R, x) {
		var head = L;
		var arg = x.R.type == "var" ? R : "(" + R + ")" ;
		return head + " (\\" + arg + ")"
	 }});
}

console.log("<html><body><table>");
console.log("<tr><td>size</td><td>term</td><td>map</td></tr>");

for (var size = 0; size < 4; size++) {
  console.log("<tr><td colspan=3><hr></td></tr>");

  var data =
      lam.c_le_atom(size, 1).map(function(term) {
        return {term: term, map: agda.map_of_term(term)};
      });

  for(var i = 0; i < data.length; i++) {
    var row = data[i];
    console.log("<tr>");
    if (i == 0) {
      console.log("<td rowspan=" + data.length + ">"+size+"</td>")
    }
    console.log("<td>" + string_of_term(row.term) + "</td><td>" + JSON.stringify(row.map) + "</td>");
    console.log("</tr>");
  }
}

console.log("</table></body></html>");
