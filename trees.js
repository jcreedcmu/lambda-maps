fullscreen();


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

var S = 15;

function fillCircle(d, x, y, r) {
  d.beginPath();
  d.arc(x, y, r, 0, 2 * Math.PI);
  d.fill();
}

function draw_term(s, pos) {
  function draw_term_off(s) {
	 draw_term(s, {x: s.pos.x + pos.x, y: s.pos.y + pos.y});
  }
  if (s.type == "var") {
	 d.fillStyle = "green";
	 d.fillRect(pos.x * S, pos.y * S, S, S);
  }
  if (s.type == "lam") {
	 d.fillStyle = "#007";
	 fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, S/3);


	 d.fillStyle = "#0f0";
	 d.fillRect(pos.x * S, (pos.y + (s.size.y - 1)) * S, S, S);
	 draw_term_off(s.B);

  }
  if (s.type == "app") {
	 d.fillStyle = "black";
	 fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, S/3);
	 d.fillStyle = "white";
	 fillCircle(d, (pos.x + (s.size.x ) / 2) * S, (1/2 + pos.y) * S, S/4);
	 draw_term_off(s.L);
	 draw_term_off(s.R);
  }
}

var terms = c_norm(3, 0);
terms.push({type: "app", L: {type: "var"}, R: {type: "var"}});
terms.push({type:"lam", B: {type: "app", L: {type: "var"}, R: {type: "var"}}});
d.translate(10, 10);
d.fillStyle = "#dddddd";
_.each(terms, function(term, i) {
  d.save();
  d.translate(i * 110, 0);
  d.fillRect(0,0,100,100);
  var m = measure_term(term);
  d.fillStyle="#def";
  d.fillRect(0,0,m.size.x*S,m.size.y*S);
  draw_term(m, {x:0, y:0});
  d.restore();
});
