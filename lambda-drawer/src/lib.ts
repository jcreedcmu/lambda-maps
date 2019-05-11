type Point = { x: number, y: number };
type BinTerm = { t: 'bin', subt?: string, L: Term, R: Term };
type MeasureBinTerm = { t: 'bin', subt?: string, L: MeasureTerm, R: MeasureTerm } & Measure;
export type Term =
  | { t: 'var' }
  | BinTerm
  | { t: 'un', B: Term, subt: string };
type Measure = { size: Point, pos: Point };
export type MeasureTerm =
  | { t: 'var' } & Measure
  | MeasureBinTerm
  | { t: 'un', B: MeasureTerm, subt: string } & Measure;


const SPACING = 20;
const DOT_SIZE = 6;
const RIGIDITY = 0.6;
const LINE_WIDTH = 1;


function offset_term(t: MeasureTerm, dx: number, dy: number) {
  return { ...t, pos: { x: t.pos.x + dx, y: t.pos.y + dy } };
}

export function measure_term(s: Term): MeasureTerm {
  switch (s.t) {
    case 'var':
      return { t: "var", size: { x: 1, y: 1 }, pos: { x: 0, y: 0 } };

    case 'bin':
      var L = measure_term(s.L);
      var R = measure_term(s.R);
      var h = Math.max(L.size.y, R.size.y);
      var w = L.size.x + R.size.x;
      return {
        t: "bin",
        subt: s.subt,
        size: { x: w, y: h + 1 },
        pos: { x: 0, y: 0 },
        L: offset_term(L, 0, 1 + (h - L.size.y)),
        R: offset_term(R, L.size.x, 1 + (h - R.size.y)),
      }

    case 'un':
      var B = measure_term(s.B);
      var h = B.size.y;
      var w = B.size.x;
      return {
        t: "un",
        subt: s.subt,
        size: { x: w, y: h + 1 },
        pos: { x: 0, y: 0 },
        B: offset_term(B, 0, 1 + (h - B.size.y)),
      }
  }
}

function fillCircle(d: CanvasRenderingContext2D, x: number, y: number, r: number): void {
  d.beginPath();
  d.arc(x, y, r, 0, 2 * Math.PI);
  d.fill();
}

function node_center(pos: Point, s: MeasureTerm): Point {
  return { x: (pos.x + (s.size.x) / 2) * SPACING, y: (1 / 2 + pos.y) * SPACING };
}

function child_center(pos: Point, ch: MeasureTerm): Point {
  var npos = { x: pos.x + ch.pos.x, y: pos.y + ch.pos.y };
  return node_center(npos, ch);
}

function bound_center(pos: Point, s: MeasureTerm): Point {
  return { x: (1 / 2 + pos.x) * SPACING, y: (pos.y + (s.size.y - 1 / 2)) * SPACING };
}

function curve(d: CanvasRenderingContext2D, src: Point, tgt: Point): void {
  d.beginPath();
  d.moveTo(src.x, src.y);
  d.bezierCurveTo(src.x, src.y, tgt.x, tgt.y - (tgt.y - src.y) * RIGIDITY, tgt.x, tgt.y);
  d.stroke();
}

function draw_edges(d: CanvasRenderingContext2D, s: MeasureTerm, pos: Point): void {
  function draw_edges_off(s: MeasureTerm) {
    draw_edges(d, s, { x: s.pos.x + pos.x, y: s.pos.y + pos.y });
  }
  switch (s.t) {
    case 'var': break;
    case 'bin': {
      const nc = node_center(pos, s);
      const Lc = child_center(pos, s.L);
      const Rc = child_center(pos, s.R);

      d.strokeStyle = 'black';
      curve(d, nc, Lc);

      d.strokeStyle = 'black';
      curve(d, nc, Rc);

      draw_edges_off(s.L);
      draw_edges_off(s.R);
    } break;

    case 'un': {
      const nc = node_center(pos, s);
      const Bc = child_center(pos, s.B);

      d.strokeStyle = 'black';
      curve(d, nc, Bc);

      draw_edges_off(s.B);
    } break;
  }
}

function draw_nodes(d: CanvasRenderingContext2D, s: MeasureTerm, pos: Point): void {
  function draw_nodes_off(s: MeasureTerm) {
    draw_nodes(d, s, { x: s.pos.x + pos.x, y: s.pos.y + pos.y });
  }
  if (s.t == 'var') return;

  d.fillStyle = 'black';
  fillCircle(d, (pos.x + (s.size.x) / 2) * SPACING, (1 / 2 + pos.y) * SPACING, DOT_SIZE);
  d.fillStyle = 'gray';
  fillCircle(d, (pos.x + (s.size.x) / 2) * SPACING, (1 / 2 + pos.y) * SPACING, DOT_SIZE - LINE_WIDTH);

  if (s.t == 'bin') {
    draw_nodes_off(s.L);
    draw_nodes_off(s.R);
  }
  else if (s.t == 'un') {
    draw_nodes_off(s.B);
  }
}

function draw_connection(d: CanvasRenderingContext2D, y: number, src: number, tgt: number, color: string) {
  d.beginPath();
  var m = (src + tgt) / 2;
  var R = (tgt - src) / 2;
  d.arc((m + 1 / 2) * SPACING, y, R * SPACING, 0, Math.PI);
  d.strokeStyle = color;
  d.stroke();
}

export function draw_term(d: CanvasRenderingContext2D, s: MeasureTerm, conns: [number, number][]) {
  d.fillStyle = "pink";
  d.fillRect(0, 0, SPACING * s.size.x, SPACING * s.size.y);
  draw_edges(d, s, { x: 0, y: 0 });
  draw_nodes(d, s, { x: 0, y: 0 });
  conns.forEach(conn => {
    draw_connection(d, (s.size.y - 1 / 2) * SPACING, conn[0], conn[1], 'black');
  });

}
