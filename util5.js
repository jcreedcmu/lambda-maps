function fullscreen() {
  c = $("#c")[0];
  d = c.getContext('2d');
  w = c.width = innerWidth;
  h = c.height = innerHeight;
}

function cconv(x) {
  var n = Math.floor(255 * x);
  if (n > 255) n = 255;
  if (n < 0) n = 0;
  return n;
}

function rgb(r, g, b) {
  return 'rgba(' + cconv(r) + ',' + cconv(g) + ',' + cconv(b) + ',1)'
}

function rgba(r, g, b, a) {
  return 'rgba(' + cconv(r) + ',' + cconv(g) + ',' + cconv(b) + ',' + a + ')'
}

function fillTextMulti(d, text, x, y) {
  var split = text.split('\n');
  split.forEach(function(line ) {
    d.fillText(line, x, y - split.length * FONT_SIZE / 2);
    y += FONT_SIZE;
  });
}

function clone(x) {
  return JSON.parse(JSON.stringify(x));
}

keytab = {
  37: "left",
  38: "up",
  39: "right",
  40: "down",
  32: "space",
  33: "pgup",
  34: "pgdn",
  35: "end",
  36: "home",
};
_.each(_.range(26), function(i ) {return keytab[65 + i] = String.fromCharCode(97 + i)});

function getKey(e) {
  var n = e.keyCode;
  if (n in keytab) {
    var prefix = "";
    if (e.ctrlKey) prefix += "C";
    if (e.altKey) prefix += "A";
    if (e.metaKey) prefix += "M";
    if (e.shiftKey) prefix += "S";
    if (prefix != "") prefix += "-";
    var keysym = prefix + keytab[n];
//    console.log(keysym);
    return keysym;
  }
  else {
    return null;
  }
}

function sqdist(p, q) {
  return (p.x - q.x) * (p.x - q.x) + (p.y - q.y) * (p.y - q.y);
}

function distance(p, q) {
  return Math.sqrt(sqdist(p, q));
}

function vmag(p) {
  return Math.sqrt(vdot(p, p));
}

function buffer(w, h) {
  var cc = $("<canvas>")[0];
  cc.width = w;
  cc.height = h;
  cc.d = cc.getContext('2d');
  return cc;
}

function isin(x, a, b) {
  return x >= a && x <= b;
}

function lerp(a, b, t) {
  return a * (1 - t) + b * t;
}

rand = Math.random;
int = Math.floor;


function relpos(e, c) {
  var off = $(c).offset();
  return {x: e.clientX - off.left, y: e.clientY - off.top};
}

function vplus(a, b) {
  return {x: a.x + b.x, y: a.y + b.y};
}

function vminus(a, b) {
  return {x: a.x - b.x, y: a.y - b.y};
}

function vscale(s, b) {
  return {x: s * b.x, y: s * b.y};
}

function vdot(a, b) {
  return a.x * b.x + a.y * b.y;
}

function vfloor(a, b) {
  return {x: Math.floor(a.x), y: Math.floor(a.y)};
}

function make_set(array) {
  return _.object((function(){var S_ITER$0 = typeof Symbol!=='undefined'&&Symbol.iterator||'@@iterator';function GET_ITER$0(v){if(v){if(Array.isArray(v))return 0;var f;if(typeof v==='object'&&typeof (f=v[S_ITER$0])==='function')return f.call(v);if((v+'')==='[object Generator]')return v;}throw new Error(v+' is not iterable')};var $D$0;var $D$1;var $D$2;var $result$0 = [], k;$D$0 = GET_ITER$0(array);$D$2 = $D$0 === 0;$D$1 = ($D$2 ? array.length : void 0);for(; $D$2 ? ($D$0 < $D$1) : !($D$1 = $D$0["next"]())["done"]; ){k = ($D$2 ? array[$D$0++] : $D$1["value"]);{$result$0.push([k, 1])}};;return $result$0})());
}

var json = JSON.stringify;
var djson = JSON.parse;

function upperFirst(x) {
  return x.charAt(0).toUpperCase() + x.slice(1);
}

function Loader() {
  this.count = 0;
  this.tasks = [];
  this.src = {};
  this.img = {};
}

Loader.prototype.add = function (task) {
  this.tasks.push(task);
  this.count--;
}

function shader(which) {
  return {
    exec: function(ld) {
    $.ajax(which + '.c', {success: function(x) {
      ld.src[which] = x;
      ld.succ();
    }});
    },
  };
}

function image(src, name) {
  return {
    exec: function(ld) {
      var im = new Image();
      im.src = src;
      im.onload = function() {
	ld.img[name] = im;
	ld.succ();
      }
    }
  };
}

Loader.prototype.done = function (k) {
  var that = this;
  this.k = k;
  this.tasks.forEach(function(x) { x.exec(that); });
}
Loader.prototype.succ = function () {
  if (++this.count == 0) {
    this.k();
  }
}

function sum(a) {
  var rv = 0;
  a.forEach(function (n) {rv += n;});
  return rv;
}
