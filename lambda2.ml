
#require "yojson";;
#require "str";;
open Yojson;;

type ('v, 'l, 'a) term = Var of 'v | Lam of 'l * ('v, 'l, 'a) term | App of 'a * ('v, 'l, 'a) term * ('v, 'l, 'a) term

type color = C0 | C1 | C2

let map = List.map
let filter = List.filter
let rec ofilter f xs = match xs with
  | [] -> []
  | x::xs ->
     match f x with
     | None -> ofilter f xs
     | Some y -> y :: ofilter f xs

type nzcolor = N1 | N2
let int_of_color = (function C0 -> 0 | C1 -> 1 | C2 -> 2)
let int_of_nzcolor = (function N1 -> 1 | N2 -> 2)
let color_of_int n = (function 0 -> C0 | 1 -> C1 | 2 -> C2 | _ -> raise (Failure "nope")) (n mod 3)
let plus c d = color_of_int (int_of_color c + int_of_color d)
let act c d = color_of_int (int_of_nzcolor c + int_of_color d)

let ( |> ) x f = f x

let splits n f =
  let rec go m =
    if m < 0
    then []
    else f (m, (n-m)) @ go (m-1)
  in
  go n



let flatmap f xs = List.flatten (map f xs)

(* strict splits, require both sides >= 1 *)
let ssplits n f = splits (n-2) (fun (a, b) -> f (a+1, b+1))


type bare = (unit, unit, unit) term
let bVar = Var()
let bLam t = Lam((), t)
let bApp(t, t') = App((), t, t')


(* enumerate bridgeless planar terms with [vars] free variables and no
   more than [lams] lambdas, and how many lambdas each uses *)
let rec get_terms (vars: int) (lams: int): bare list =
  (if lams = 0 && vars = 1 then [bVar] else [])
  @ (if lams >= 1 then get_terms (vars+1) (lams-1) |> map (fun t -> bLam t) else [])
  @ ssplits vars (fun (a, b) -> splits lams
                 (fun (la, lb) -> get_terms a la |> flatmap
                 (fun ta -> get_terms b lb |> map
                 (fun tb -> bApp(ta, tb)))))


type chiral = (unit, nzcolor, nzcolor) term
let rot c cs = cs |> map (fun d -> act c d)

let rec get_chi_terms (vars: int) (lams: int): (chiral * color list) list =
  (if lams = 0 && vars = 1 then [bVar, [C0]] else [])
  @ (if lams >= 1 then get_chi_terms (vars+1) (lams-1)
                       |> flatmap (fun (t, cs) ->
                              match cs with
                              | C1::cs_tl -> [Lam(N1, t), rot N1 cs_tl]
                              | C2::cs_tl -> [Lam(N2, t), rot N2 cs_tl]
                              | _ -> []) else [])
  @ ssplits vars (fun (va, vb) -> splits lams
                 (fun (la, lb) -> get_chi_terms va la |> flatmap
                 (fun (ta, ga) -> get_chi_terms vb lb |> flatmap
                 (fun (tb, gb) -> [App(N1, ta, tb), rot N2 ga @ rot N1 gb;
                                   App(N2, ta, tb), rot N1 ga @ rot N2 gb]))))


let rec get_normal_chi_terms (vars: int) (lams: int): (chiral * color list) list =
  (if lams >= 1 then get_normal_chi_terms (vars+1) (lams-1)
                     |> flatmap (fun (t, cs) ->
                            match cs with
                            | C1::cs_tl -> [Lam(N1, t), rot N1 cs_tl]
                            | C2::cs_tl -> [Lam(N2, t), rot N2 cs_tl]
                            | _ -> []) else [])
  @ get_atomic_chi_terms vars lams

and get_atomic_chi_terms (vars: int) (lams: int): (chiral * color list) list =
  (if lams = 0 && vars = 1 then [bVar, [C0]] else [])
  @ ssplits vars (fun (va, vb) -> splits lams
                 (fun (la, lb) -> get_atomic_chi_terms va la |> flatmap
                 (fun (ta, ga) -> get_normal_chi_terms vb lb |> flatmap
                 (fun (tb, gb) -> [App(N1, ta, tb), rot N2 ga @ rot N1 gb;
                                   App(N2, ta, tb), rot N1 ga @ rot N2 gb]))))

let color_cmp x y = int_of_color x - int_of_color y
let sort_colors = List.sort color_cmp
let opp = (function N1 -> C2 | N2 -> C1)
let copp = (function C0 -> C0 | C1 -> C2 | C2 -> C1)

let ( ||| ) f g = fun a b c d -> let res = f a b in if res <> 0 then res else g c d

let rec lex_cmp cmp a b = match (a, b) with
  | ([], []) -> 0
  | ([], x::xs) -> -1
  | (x::xs, []) -> 1
  | (x::xs, y::ys) -> (cmp ||| lex_cmp cmp) x y xs ys

let uniq xs = match xs with
  | [] -> []
  | x::xs ->
     let rec aux last rest = match rest with
       | [] -> []
       | r::rs -> if last = r then aux r rs else r :: aux r rs
     in x :: aux x xs

let collect xs = match xs with
  | [] -> []
  | (k, v)::xs ->
     let rec aux last_key values rest = match rest with
       | [] -> [last_key, List.rev values]
       | (k0,v0)::rs -> if last_key = k0
                        then aux last_key (v0::values) rs
                        else (last_key, List.rev values) :: aux k0 [v0] rs
     in aux k [v] xs

let rec enum_contexts n = match n with
  | 1 -> [[C0]]
  | n -> let tack_on nzc ctx = sort_colors (opp nzc :: (ctx |> map (act nzc))) in
         (enum_contexts (n-1)
          |> map (fun ctx -> [tack_on N1 ctx; tack_on N2 ctx])
          |> List.flatten
          |> List.sort (lex_cmp color_cmp)
          |> uniq)

let string_of_color = function C0 -> "." | C1 -> "|" | C2 -> "="
let numstring_of_color = function C0 -> "0" | C1 -> "1" | C2 -> "2"

let picture xss =
  xss
  |> List.map (fun xs -> xs
                         |> List.map string_of_color
                         |> String.concat "" |> (fun x -> x ^ "\n"))
  |> String.concat ""

let rec bare_term_of_term t = match t with
  | Var _ -> bVar
  | Lam(_, t) -> bLam(bare_term_of_term t)
  | App(_, a, b) -> bApp(bare_term_of_term a, bare_term_of_term b)

let rec bare_term_cmp t1 t2 = match (t1, t2) with
  | (Var (), Var ()) -> 0
  | (Lam((), u1), Lam((), u2)) -> bare_term_cmp u1 u2
  | (App((), u1, v1), App((), u2, v2)) -> (bare_term_cmp ||| bare_term_cmp) u1 u2 v1 v2
  | (Var _, Lam _) -> 1
  | (Lam _, Var _) -> -1
  | (Var _, App _) -> 1
  | (App _, Var _) -> -1
  | (Lam _, App _) -> 1
  | (App _, Lam _) -> -1

(*
(* Every term with some free variables has a 'coloring' profile: which colorings of free variables
   make it well-colored. Here we enumerate the distinct profiles for all terms with 3 variables and 4 lambdas:
*)

let out = get_normal_chi_terms 3 4
          |> List.map (fun (t, c) -> (bare_term_of_term t, c))
          |> List.sort (fun (t1, c1) (t2, c2) -> bare_term_cmp t1 t2)
          |> collect
          |> List.map (fun (a, b) -> b)
          |> List.map (fun colorings -> colorings |> List.sort (lex_cmp color_cmp) |> uniq)
          |> List.sort (lex_cmp (lex_cmp color_cmp)) |> uniq

(* I get the same answer if I increase 4 to 5 *)
 *)

let pABC = [[C0; C1; C1]; [C0; C2; C2]; [C1; C0; C1]; [C1; C1; C0]; [C2; C0; C2]; [C2; C2; C0]]
let pABCZ = [[C0; C0; C0]; [C0; C1; C1]; [C0; C2; C2]; [C1; C0; C1]; [C1; C1; C0]; [C2; C0; C2]; [C2; C2; C0]]

let _ = if false
        then
          let collected =  get_normal_chi_terms 4 3
                           |> List.map (fun (t, c) -> (bare_term_of_term t, c))
                           |> List.sort (fun (t1, c1) (t2, c2) -> bare_term_cmp t1 t2)
                           |> collect in

          let out = collected
                    |> List.map (fun (a, b) -> b)
                    |> List.map (fun colorings -> colorings |> List.sort (lex_cmp color_cmp) |> uniq)
                    |> List.sort (lex_cmp (lex_cmp color_cmp)) |> uniq in
          ()
        else ()

(* let search = collected *)
(*              |> List.map (fun (t, colorings) -> (t, colorings |> List.sort (lex_cmp color_cmp) |> uniq)) *)
(*              |> filter (fun (t, profile) -> profile = pABCZ) *)
(*              |> List.map (fun (t, profile) -> t) *)
(*              |> List.hd *)

type tree = TLeaf | TNode of tree * tree
let rec string_of_tree t = match t with
  | TLeaf -> "*"
  | TNode (t1, t2) -> "[" ^ string_of_tree t1 ^ string_of_tree t2 ^ "]"

(* enumerate all the trees with n internal nodes *)
let rec enum_trees n =
    if n = 0 then [TLeaf]
    else splits (n-1)
                (fun (a, b) ->
                  enum_trees a |> flatmap (fun ta -> enum_trees b |> map (fun tb -> TNode(ta, tb))))

let cross t1 t2 = t1 |> flatmap (fun x1 -> t2 |> map (fun x2 -> (x1, x2)))

let colorings_of_tree tree =
  let rec aux c t = match t with
    | TLeaf -> [[c]]
    | TNode(t1, t2) -> (cross (aux (plus c C1) t1) (aux (plus c C2) t2)
                        @ cross (aux (plus c C2) t1) (aux (plus c C1) t2))
                       |> map (fun (x, y) -> x @ y)
  in
  aux C0 tree

(* "is this coloring representative?" *)
(* we want to pick out representatives of the equivalence classes
under the opp, the involution that interchanges C1 and C2. *)
let is_rep coloring = lex_cmp color_cmp coloring (map copp coloring) <> 1
(*
# is_rep [C0; C1];;
- : bool = true
# is_rep [C0; C2];;
- : bool = false
# is_rep [C0; C0];;
- : bool = true
 *)

let string_of_coloring coloring = coloring |> List.map numstring_of_color |> String.concat ""

let jstr s = `String s
let jarr s = `List s

(* census of all colorings possible for a given tree, keyed by tree *)
let keyed_census n = enum_trees n |> map (fun t -> (t, colorings_of_tree t |> filter is_rep |> map string_of_coloring))

(* just the colorings, forgetting what tree they came from *)
let census n = map snd (keyed_census n)

let census_json n = census n |> map (fun slist -> slist |> map jstr |> jarr) |> jarr

let write n =
  let json = census_json n in
  let json_string = to_string json in
  let oc = open_out "data.json"  in
  Printf.fprintf oc "%s\n" json_string;
  close_out oc

let rec upd_assoc k f xs = match xs with
  | [] -> [k, f None]
  | (k',v) :: xs -> if k = k'
                    then (k, f (Some v)) :: xs
                    else (k', v) :: upd_assoc k f xs

let counts_of_colorings n = census n

let bump = function None -> 1
                  | Some n -> n+1

(* basically uniq -c *)
let group_and_count xs = xs |> List.fold_left (fun acc x -> acc |> upd_assoc x bump) [];;

let intersection xs ys = xs |> filter (fun x -> List.mem x ys)
let list_max = List.fold_left max 0
let list_min = List.fold_left min 1000000

(*

Every coloring C has a *frequency*, the number of trees such that C is
a valid coloring for T.

The 'max' of a treepair U is maximum frequency of a coloring that
satisfies both trees in U.

"maxes" is a list of all numbers that are a max of some treepair.

The minimum of maxes is a number that represents how rare the rarest
necessary coloring is. If we take all colorings that occur at least
that often, they're enough to color every treepair.

"colorings_for_min" is a list of (number of colorings, max of treepair)
where by construction the second element is the minimum of maxes.

"challenges" is basically the constructive witnesses for this set.

Conjecture 0: min-of-maxes is always n, the number of internal nodes of the trees in question.
Conjecture 1: the fst of every element of colorings for min is 1.
Conjecture 2: the length of colorings_for_min is 2 * n + 4
Conjecture 3: the colorings in this set all occur exactly twice, due to vertical flip symmetry,
and the n + 2 distinct colorings are
(for odd n)
1211111 ... 1  Ln <-> v * L(n-1)
1 ... 1111121  Rn <-> R(n-1) * v

1020 ... 0000  v * L(n-1) <-> R1 * L(n-2)
01020 ... 000  R1 * L(n-2) <-> R2 * L(n-3)
...
0000 ... 0102  R(n-1) * v <-> R(n-2) * L1
1000 ... 0002  Rn <-> Ln

(for even n)
1011111 ... 1 Ln <-> v * L(n-1)
1 ... 1111101 Rn <-> R(n-1) * v

1010 ... 0000 v * L(n-1) <-> R1 * L(n-2)
01010 ... 000 R1 * L(n-2) <-> R2 * L(n-3)
...
0000 ... 0101 R(n-1) * v <-> R(n-2) * L1
1000 ... 0001 Rn <-> Ln

where
L0 = R0 = v
L(n+1) = Ln * v
R(n+1) = v * Ln

I can get these lists by doing things like:
(info_of 6).challenges |> map snd |> List.sort String.compare |> uniq;;

 *)
type info = {
    maxes: int list;
    colorings_for_min: (int * int) list;
    length: int;
    challenges: ((string * string) * string) list;
  }

let info_of nnn =
  let kcen = keyed_census nnn in
  let cen = map snd kcen in
  let counts = cen |> List.flatten |> group_and_count in
  let table = cross cen cen
              |> map (fun (x, y) -> intersection x y
                                    |> (fun cngs ->
                        (List.length cngs, cngs |> map (fun cng -> List.assoc cng counts) |> list_max))) in
  let maxes = table |> List.map (fun (x, y) -> y) |> List.sort (fun x y -> x - y) |> uniq in
  let min_of_maxes = list_min maxes in
  let colorings_for_min = table |> filter (fun (x, y) -> y = min_of_maxes) in
  let challenges = cross kcen kcen
                   |> map (fun ((t1, cngs1), (t2, cngs2)) -> ((t1, t2), intersection cngs1 cngs2))
                   |> ofilter (fun ((t1, t2), cngs) -> match cngs with [x] -> Some ((t1, t2), x) | _ -> None)
                   |> filter (fun ((t1, t2), cng) -> List.assoc cng counts = min_of_maxes)
                   |> map (fun ((t1, t2), cng) -> ((string_of_tree t1, string_of_tree t2), cng)) in
  {maxes=maxes; colorings_for_min=colorings_for_min; length=List.length colorings_for_min; challenges=challenges}



(* interesting: when a tree-pair has a less common most-common-coloring, it tends to have fewer colorings*)
(* let _ = table |> filter (fun (x, y) -> y = 4);; (\* (1, 4) *\) *)
(* let _ = table |> filter (fun (x, y) -> y = 5);; (\* (1, 5), (2, 5) *\) *)
(* let _ = table |> filter (fun (x, y) -> y = 6);; (\* (1, 6), (2, 6), (4, 6), (8, 6) *\) *)


(*
 cat data.json | jq 'reduce .[][] as $x ({}; . as $old | . + {($x): (($old[$x] // 0) + 1)} )'

cat data.json | jq 'reduce .[][] as $x ({}; . as $old | . + {($x): (($old[$x] // 0) + 1)} ) | to_entries | sort_by(.value)| [.[] |select(.value == 12)] | length'

 cat data.json | jq -r 'reduce .[][] as $x ({}; . as $old | . + {($x): (($old[$x] // 0) + 1)} ) | to_entries | sort_by(.value) | .[]|.key + " " +(.value |tostring)'
 *)
