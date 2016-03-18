var PERROW = 7;
var BLOCK = {x: 120, y: 200};
var MARGIN = 5;
var S = 13;
var DOT_SIZE = 4.7;
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

var light_blue = "#19f";
var dark_blue = "#227";
var light_purple = "#8d1aef"
var light_brown = "#851";
var colors = {
  app:  {left: light_blue,    right: light_purple, fill: "#fff", stroke: light_brown },
  slam: {left: light_blue,    right: "#e00", fill: dark_blue },
  lam:  {left: light_blue,    right: "#e00", fill: light_brown },
}

colors.neg = colors.app;
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
}

function draw_nodes(d, s, pos) {
  function draw_nodes_off(s) {
	 draw_nodes(d, s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
  }
  if (s.type == "bin") {
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
	 draw_nodes_off(s.L);
	 draw_nodes_off(s.R);
  }
}

function draw_connection(d, y, from, to) {
  d.beginPath();
  var m = (from + to) / 2;
  var R = (to - from) / 2;
  d.arc((m + 1/2) * S, y, R * S, 0, Math.PI);
  d.strokeStyle = light_blue;
  d.stroke();
}

function decode(s) {
  return s.replace(/\\u([0-9a-f]{4})/g, function(x, y) {
	 return String.fromCharCode(parseInt(y, 16));
  });
}

function draw_term(d, s, conns) {
  draw_edges(d, s, {x:0,y:0});
  draw_nodes(d, s, {x:0,y:0});
  _.each(conns, function(conn) {
	 draw_connection(d, (s.size.y - 1/2) * S, conn[0], conn[1]);
  });
}

_.each(data, function(datum, i) {
  var term = datum.term;
  var tp = datum.type;
  var c = $("<canvas>");

  c.appendTo($("body"));
  c[0].width = 2 * BLOCK.x;
  c[0].height = BLOCK.y;
  var d = c[0].getContext("2d");

  d.lineWidth = 2;

  d.save();
  var m = measure_term(term.tree);
  d.translate(BLOCK.x / 2 -  S * m.size.x /2, 0);
  draw_term(d, m, term.conn);
  d.restore();

  d.fillText(decode(datum.type_string), 10, BLOCK.y - 25);
  d.fillText(decode(datum.term_string), 10, BLOCK.y - 40);
  d.fillStyle = "#aaa";
  d.fillRect(0,BLOCK.y - 15, BLOCK.x * 2, 1);

  d.save();
  d.translate(BLOCK.x, 0);
  var m = measure_term(tp.tree);
  d.translate(BLOCK.x / 2 -  S * m.size.x /2, 0);
  draw_term(d, m, tp.conn);
  d.restore();

});
