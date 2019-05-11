
import { measure_term, draw_term } from './lib';

const c = document.createElement('canvas');
const body = document.getElementsByTagName('body');
if (body == undefined) {
  throw 'nope';
}
body[0].append(c);
c.width = innerWidth;
c.height = innerHeight;
const d = c.getContext("2d")!;
draw_term(d, measure_term({ t: 'bin', L: { t: 'bin', L: { t: 'var' }, R: { t: 'var' } }, R: { t: 'var' } }), [[0, 1], [0, 2]]);
