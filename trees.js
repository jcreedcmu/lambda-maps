fullscreen();
var PERROW = 7;
var BLOCK = {x: 120, y: 160};
var MARGIN = 5;
var S = 12.5;
var RIGIDITY = 0.6;

function offset_term(t, dx, dy) {
  var rv = _.extend({}, t, {pos:{x:t.pos.x+dx,y:t.pos.y+dy}});
  return rv;
}

function measure_term(s) {
  if (s.type == "var") {
	 return {type: "var", size:{x:1,y:1}, pos: {x:0,y:0}};
  }
  if (s.type == "bin") {
	 var L = measure_term(s.L);
	 var R = measure_term(s.R);
	 var h = Math.max(L.size.y, R.size.y);
	 var w = L.size.x + R.size.x;
	 return {type: "bin",
				subtype: s.subtype,
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

function curve(d, from, to) {
  d.beginPath();
  d.moveTo(from.x, from.y);
  d.bezierCurveTo(from.x, from.y, to.x, to.y - (to.y - from.y) * RIGIDITY, to.x, to.y);
  d.stroke();
}

function draw_edges(s, pos) {
  function draw_edges_off(s) {
	 draw_edges(s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
  }
  if (s.type == "bin") {
	 var nc = node_center(pos, s);
	 var Lc = child_center(pos, s, "L");
	 var Rc = child_center(pos, s, "R");

	 d.strokeStyle = "#07f";
	 curve(d, nc, Lc);

	 d.strokeStyle = s.subtype == "app" ? "#70f" : "#e00";
	 curve(d, nc, Rc);

	 draw_edges_off(s.L);
	 draw_edges_off(s.R);
  }
}

function draw_nodes(s, pos) {
  function draw_nodes_off(s) {
	 draw_nodes(s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
  }
  if (s.type == "bin") {
	 d.fillStyle = "#000";
	 fillCircle(d, (pos.x + (s.size.x) / 2) * S, (1/2 + pos.y) * S, S/3);
	 if (s.subtype == "app") {
		d.fillStyle = "white";
		fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, S/4);
	 }
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

function draw_term(s, conns) {
  draw_edges(s, {x:0,y:0});
  draw_nodes(s, {x:0,y:0});
  _.each(conns, function(conn) {
	 draw_connection((s.size.y - 1/2) * S, conn[0], conn[1]);
  });
}

// var terms = c_norm(4, 0);

d.translate(MARGIN, MARGIN);
d.fillStyle = "#dddddd";
d.lineWidth = 1.7;
_.each(data, function(term, i) {
  d.save();
  d.translate((i % PERROW) * (BLOCK.x + MARGIN), Math.floor(i/PERROW) * (BLOCK.y + MARGIN));
  //  d.fillRect(0,0,100,100);
  var m = measure_term(term.tree);
  d.translate(BLOCK.x / 2 -  S * m.size.x /2, 0);
//  d.fillStyle="#e3e9f0";
//  d.fillRect(0,0,m.size.x*S,m.size.y*S);
  draw_term(m, term.conn);
  d.restore();
});
