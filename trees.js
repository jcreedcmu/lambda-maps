fullscreen();
var PERROW = 10;
var BLOCK = {x: 120, y: 200};
var MARGIN = 5;
var S = 15;
function offset_term(t, dx, dy) {
  var rv = _.extend({}, t, {pos:{x:t.pos.x+dx,y:t.pos.y+dy}});
  return rv;
}

function measure_term(s) {
  if (s.type == "var") {
	 return {type: "var", size:{x:1,y:1}, pos: {x:0,y:0}};
  }
  if (s.type == "lam") {
	 var B = measure_term(s.B);
	 return {type: "lam",
				size:{x:B.size.x+1, y:B.size.y+1},
				pos: {x:0, y:0},
				B: offset_term(B, 1, 1),
			  }
  }
  if (s.type == "app") {
	 var L = measure_term(s.L);
	 var R = measure_term(s.R);
	 var h = Math.max(L.size.y, R.size.y);
	 var w = L.size.x + R.size.x;
	 return {type: "app",
				size:{x:w, y:h+1},
				pos: {x:0, y:0},
				L: offset_term(L, 0, 1 + (h - L.size.y)),
				R: offset_term(R,  L.size.x, 1 + (h - R.size.y)),
			  }
  }
}



function fillCircle(d, x, y, r) {
  d.beginPath();
  d.arc(x, y, r, 0, 2 * Math.PI);
  d.fill();
}

function node_center(pos, s) {
  return {x: (pos.x + (s.size.x) / 2) * S, y: (1/2 + pos.y) * S};
}

function child_center(pos, s, c) {
  var ch = s[c];
  var npos = {x:pos.x + ch.pos.x, y:pos.y + ch.pos.y};
  return node_center(npos, ch);
}

function bound_center(pos, s) {
  return {x: (1/2 + pos.x) * S, y: (pos.y + (s.size.y - 1/2)) * S};
}

function draw_edges(s, pos) {
  function draw_edges_off(s) {
	 draw_edges(s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
  }
  if (s.type == "lam") {
	 var nc = node_center(pos, s);
	 var Bc = child_center(pos, s, "B");
	 var bc = bound_center(pos, s);

	 d.beginPath();
	 d.strokeStyle = "#07f";
	 d.moveTo(nc.x, nc.y);
	 d.lineTo(bc.x, bc.y);
	 d.stroke();

	 d.beginPath();
	 d.strokeStyle = "#e00";
	 d.moveTo(nc.x, nc.y);
	 d.lineTo(Bc.x, Bc.y);
	 d.stroke();

	 draw_edges_off(s.B);

  }
  if (s.type == "app") {
	 var nc = node_center(pos, s);
	 var Lc = child_center(pos, s, "L");
	 var Rc = child_center(pos, s, "R");

	 d.beginPath();
	 d.strokeStyle = "#07f";
	 d.moveTo(nc.x, nc.y);
	 d.lineTo(Lc.x, Lc.y);
	 d.stroke();

	 d.beginPath();
	 d.strokeStyle = "#70f";
	 d.moveTo(nc.x, nc.y);
	 d.lineTo(Rc.x, Rc.y);
	 d.stroke();


	 draw_edges_off(s.L);
	 draw_edges_off(s.R);
  }
}

function pstring(s) {
  return traverse(s, {
	 vor: function(x) { return ")" },
	 lam: function(B, x) { return "(" + B; },
	 app: function(L, R, x) {
		return L + R;
	 }});
}

function connections(s) {
  var ps = pstring(s);
  var stack = [];
  var rv = [];
  for (var i = 0; i < ps.length; i++) {
	 if (ps[i] == "(") stack.push(i);
	 if (ps[i] == ")") {
		var start = stack.pop();
		rv.push([start, i]);
	 }
  }
  return rv;
}

function draw_nodes(s, pos) {
  function draw_nodes_off(s) {
	 draw_nodes(s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
  }
  if (s.type == "lam") {
	 d.fillStyle = "#009";
	 fillCircle(d, (pos.x + (s.size.x) / 2) * S, (1/2 + pos.y) * S, S/3);
	 draw_nodes_off(s.B);
  }
  if (s.type == "app") {
	 d.fillStyle = "black";
	 fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, S/3);
	 d.fillStyle = "white";
	 fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, S/4);
	 draw_nodes_off(s.L);
	 draw_nodes_off(s.R);
  }
}

function draw_connection(y, from, to) {
  d.beginPath();
  var m = (from + to) / 2;
  var R = (to - from) / 2;
  d.arc((m + 1/2) * S, y, R * S, 0, Math.PI);
  d.strokeStyle = "#07f";
  d.stroke();
}

function draw_term(s) {
  draw_edges(s, {x:0,y:0});
  draw_nodes(s, {x:0,y:0});
  _.each(connections(s), function(conn) {
	 draw_connection((s.size.y - 1/2) * S, conn[0], conn[1]);
  });
}


var terms = c_norm(4, 0);
d.translate(MARGIN, MARGIN);
d.fillStyle = "#dddddd";
d.lineWidth = 1.5;
_.each(terms, function(term, i) {
  d.save();
  d.translate((i % PERROW) * (BLOCK.x + MARGIN), Math.floor(i/PERROW) * (BLOCK.y + MARGIN));
//  d.fillRect(0,0,100,100);
  var m = measure_term(term);
  d.translate(BLOCK.x / 2 -  S * m.size.x /2, 0);
  d.fillStyle="#e3e9f0";
  d.fillRect(0,0,m.size.x*S,m.size.y*S);
  draw_term(m);
  d.restore();
});
