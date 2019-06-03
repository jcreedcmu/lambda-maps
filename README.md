## Dumping-ground for Lambda/Maps ideas

There's some really cool correspondences between lambda terms and combinatorial maps. Not maps in the sense of mappings --- lambda-terms *are* those, obviously, but maps in the sense of "every planar map can be 4-colored".

I believe the original one describing the relationship is

* [Asymptotics and random sampling for BCI and
BCK lambda terms](https://dmg.tuwien.ac.at/dgardy/Papers/LogiqueQuantitative/BCI.pdf)

and some other papers I enjoyed reading were:
* [A correspondence between rooted planar maps and normal planar lambda terms](http://arxiv.org/abs/1408.5028)
* [Linear lambda terms as invariants of rooted trivalent maps](http://arxiv.org/abs/1512.06751)
* [Counting isomorphism classes of β-normal linear lambda terms](http://arxiv.org/abs/1509.07596)

### The code

I wrote some code for visualizing terms and maps which is *very* sketchy. The ocaml code depends on `yojson` which I installed with `opam`. What I run is
```
$ OCAMLFIND_CONF=~/.ocamlfind.conf rlwrap ocaml
#use "lambda.ml";;
```
with my `~/.ocamlfind.conf` being
```
destdir="/usr/local/lib/ocaml/4.02.3"
path="/usr/local/lib/ocaml/4.02.3:/usr/lib/ocaml:/usr/lib/ocaml/METAS:/home/jcreed/.opam/system/lib"
```
which differs from `/etc/ocamlfind.conf` only in that I've added the `.opam/system/lib` directory in my homedir to the path. I don't know if there's a cleaner way of doing this, but this worked for me.

The `#use "lambda.ml"` generates `data.js` in the current directory, which is used by `trees.html`. If you go and view that in a browser after running the ocaml, it should display a bunch of lovely tree diagrams.

### The images

The images in `nb` are just like an infinite personal whiteboard session. I bias heavily towards saving just-in-case without filtering for quality. I wouldn't expect them to necessarily make much sense if I were you.
