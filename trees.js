var PERROW = 7;
var BLOCK = {x: 150, y: 200};
var MARGIN = 5;
var S = 10;
var DOT_SIZE = 3;
var RIGIDITY = 0.6;
var LINE_WIDTH = 1.5;

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
  if (s.type == "un") {
	 var B = measure_term(s.B);
	 var h = B.size.y;
	 var w = B.size.x;
	 return {type: "un",
				subtype: s.subtype,
				size:{x:w, y:h+1},
				pos: {x:0, y:0},
				B: offset_term(B, 0, 1 + (h - B.size.y)),
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

var orange = "#fa0";
var light_blue = "#19f";
var dark_blue = "#227";
var light_purple = "#8d1aef"
var pink = "#e965db"
var magenta = "#e3258c"
var light_brown = "#851";
var loop_closer = "#ccc";
var colors = {
  app:  {left: light_blue,    right: light_purple, fill: "#fff", stroke: light_brown },
  slam: {left: light_blue,    right: "#e00", fill: dark_blue },
  lam:  {left: light_blue,    right: "#e00", fill: light_brown },
  neg:  {left: light_purple,    right: light_blue, fill: "#fff", stroke: light_brown },
  lamv: {left: orange,    right: loop_closer, fill: dark_blue },
  lame: {left: light_purple,    right: orange, fill: light_brown },
  fuse: {left: light_purple,    right: orange, fill: "#fff", stroke: light_brown },
  marker: {left: pink,    right: orange, fill: magenta},
  marker2: {left: pink,    right: loop_closer, fill: "#fff", stroke: magenta},
}


colors.pos = colors.lam;
colors.spos = colors.slam;

function draw_edges(d, s, pos) {
  function draw_edges_off(s) {
	 draw_edges(d, s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
  }
  if (s.type == "bin") {
	 var nc = node_center(pos, s);
	 var Lc = child_center(pos, s, "L");
	 var Rc = child_center(pos, s, "R");

	 d.strokeStyle = colors[s.subtype].left;
	 curve(d, nc, Lc);

	 d.strokeStyle = colors[s.subtype].right;
	 curve(d, nc, Rc);

	 draw_edges_off(s.L);
	 draw_edges_off(s.R);
  }
  if (s.type == "un") {
	 var nc = node_center(pos, s);
	 var Bc = child_center(pos, s, "B");

	 d.strokeStyle = colors[s.subtype].left;
	 curve(d, nc, Bc);

	 draw_edges_off(s.B);
  }
}

function draw_nodes(d, s, pos) {
  function draw_nodes_off(s) {
	 draw_nodes(d, s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
  }
  if (s.type == "bin" || s.type =="un") {
	 if (colors[s.subtype].stroke != null) {
		d.fillStyle = colors[s.subtype].stroke;
		fillCircle(d, (pos.x + (s.size.x) / 2) * S, (1/2 + pos.y) * S, DOT_SIZE);
 		d.fillStyle = colors[s.subtype].fill;
		fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, DOT_SIZE - LINE_WIDTH);
	 }
	 else {
 		d.fillStyle = colors[s.subtype].fill;
		fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, DOT_SIZE);
	 }
	 if (s.type == "bin") {
		draw_nodes_off(s.L);
		draw_nodes_off(s.R);
	 }
	 else if (s.type == "un") {
		draw_nodes_off(s.B);
	 }
  }
}

function draw_connection(d, y, from, to, color) {
  d.beginPath();
  var m = (from + to) / 2;
  var R = (to - from) / 2;
  d.arc((m + 1/2) * S, y, R * S, 0, Math.PI);
  d.strokeStyle = color;
  d.stroke();
}

function decode(s) {
  return s.replace(/\\u([0-9a-f]{4})/g, function(x, y) {
	 return String.fromCharCode(parseInt(y, 16));
  });
}

function connection_color(f1, f2) {
  function subnormal(f) {
	 return (f[0] == "right" && f[1] == "app") || (f[0] == "left" && f[1] == "neg");
  }
  if (f1[0] == "left" && f1[1] == "lame") return light_purple;
  if (f1[0] == "left" && f1[1] == "fuse") return light_purple;
  if (f1[0] == "right" && f1[1] == "fuse") return orange;
  if (f1[0] == "right" && f1[1] == "lame") return orange;
  if (f1[0] == "left" && f1[1] == "marker") return pink;
  if (f1[0] == "left" && f1[1] == "marker2") return pink;
  if (f1[0] == "right" && f1[1] == "marker2") return loop_closer;
  if (f1[0] == "right" && f1[1] == "marker") return orange;
  if (f1[0] == "left" && f1[1] == "lamv") return orange;
  if (f1[0] == "right" && f1[1] == "lamv") return loop_closer;
  return subnormal(f1) || subnormal(f2) ? light_purple : light_blue;
}

function draw_term(d, s, conns, front) {
  draw_edges(d, s, {x:0,y:0});
  draw_nodes(d, s, {x:0,y:0});
  _.each(conns, function(conn) {
	 draw_connection(d, (s.size.y - 1/2) * S, conn[0], conn[1], connection_color(front[conn[0]], front[conn[1]]));
  });
}

_.each(data, function(datum, i) {
  var term = datum.term;
  var tp = datum.type;
  var c = $("<canvas>");

  c.appendTo($("body"));
  c[0].width = 3 * BLOCK.x;
  c[0].height = BLOCK.y;
  var d = c[0].getContext("2d");

  d.lineWidth = 2;

  if (!datum.regular1) {
	 d.fillStyle = "#def";
	 if (!datum.regular2) {
		d.fillStyle = "#dfd";
	 }
	 d.fillRect(0, 0, 3 * BLOCK.x, BLOCK.y);
  }
  else if (!datum.regular2) {
	 d.fillStyle = "#ff7";
	 d.fillRect(0, 0, 3 * BLOCK.x, BLOCK.y);
  }

  if (datum.orientable) {
	 d.fillStyle = "#fed";
	 d.fillRect(2 * BLOCK.x, 0, BLOCK.x, BLOCK.y);
  }

  d.fillStyle = "black";

  d.save();
  var m = measure_term(term.tree);
  d.translate(BLOCK.x / 2 -  S * m.size.x /2, 0);
  draw_term(d, m, term.conn, term.front);
  d.restore();

  d.fillText(decode(datum.type_string), 10, BLOCK.y - 25);
  d.fillText(decode(datum.term_string), 10, BLOCK.y - 40);
  d.fillText(JSON.stringify(datum.dir_vars), 10, BLOCK.y - 55);
  d.fillStyle = "#aaa";
  d.fillRect(0,BLOCK.y - 15, BLOCK.x * 3, 1);
  d.fillRect(BLOCK.x * 3 - 1,0, 1, BLOCK.y);

  d.save();
  d.translate(BLOCK.x, 0);
  var m = measure_term(tp.tree);
  d.translate(BLOCK.x / 2 -  S * m.size.x /2, 0);
  draw_term(d, m, tp.conn, tp.front);
  d.restore();

  var trin = datum.trin;
  d.save();
  d.translate(2 * BLOCK.x, 0);
  var m = measure_term(trin.tree);
  d.translate(BLOCK.x / 2 -  S * m.size.x /2, 0);
  draw_term(d, m, trin.conn, trin.front);
  d.restore();

});
