#require "yojson";;
open Yojson;;

type lam_info = LITop | LIMid
type term = Var of int | Lam of lam_info * term | App of term * term

type 'a tree = Un of string * 'a tree | Bin of string * 'a tree * 'a tree | Leaf of 'a

(* ----------------------------------- *)
(* Term Enumeration *)
(* ----------------------------------- *)

let splits n f =
  let rec go m = if m < 0
                 then []
                 else f (m, (n-m)) @ go (m-1)
  in
  go n

let list_splits xs f =
  let rec go us_rev vs = f (List.rev us_rev, vs) @ (
      match vs with
      | [] -> []
      | v::vs' -> go (v::(us_rev)) vs'
    )
  in
  go [] xs

let linear_splits xs f =
  let rec go us_rev vs_rev xs' = match xs' with
    | [] -> f (List.rev us_rev, List.rev vs_rev)
    | x::xs'' -> go (x::us_rev) vs_rev xs'' @ go us_rev (x::vs_rev) xs''
  in
  go [] [] xs

let rec cross a b = match a with
  | [] -> []
  | h::tl -> List.map (fun bx -> (h, bx)) b @ cross tl b

let infer_tops term =
  let rec go term top = match term with
    | Lam (_, body) -> Lam(top, go body LIMid)
    | App (lt, rt) -> App(go lt LIMid, go rt LITop) (* first branch shouldn't have any lambdas anyway *)
    | Var db -> Var db
  in
  go term LITop

let enumerator var_extend var_splits =
  let rec enum_normal lams free  =
    let lamcase = if lams = 0
                  then []
                  else List.map (fun x -> Lam (LIMid, x)) (enum_normal (lams-1) (var_extend free))
    in lamcase @ enum_atomic lams free
  and enum_atomic lams free  = match (lams, free) with
    | (0,[x]) -> [Var x]
    | (_,_) -> let branches =
                 splits lams (fun (lams1, lams2) ->
                          var_splits free (fun (free1, free2) ->
                                       if (free1 = []) || (free2 = [] && lams2 = 0)
                                       then []
                                       else cross (enum_atomic lams1 free1)
                                                  (enum_normal lams2 free2))) in
               List.map (fun (x, y) -> App (x, y)) branches
  in
  fun lams free -> List.map infer_tops (enum_normal lams free)

let right_extend free =
  List.map (fun x -> x + 1) free @ [0]

let left_extend free =
  0 :: List.map (fun x -> x + 1) free

(* ----------------------------------- *)
(* Type Inference *)
(* ----------------------------------- *)

type tp =
  PosArrow of lam_info * tp * tp
| NegArrow of tp * tp
| Tvar of (int * tp option) ref

let new_tvar(counter) =
  let c = !counter in
  let () = counter := c + 1 in
  ref (c, None)

let unify (t1, t2) = match (t1, t2) with
  (* Only need this one case with linear terms! *)
  | (Tvar r, _) -> let (name, _) = !r in r := (name, Some t2)
  | _ -> raise Not_found

let type_of_term tree =
  let counter = ref 0 in
  let rec go gam tree = match tree with
    | Lam (top, body) ->
       let v = new_tvar(counter) in
       PosArrow (top, Tvar v, go (v::gam) body)
    | App (lt, rt) ->
       let v = new_tvar(counter) in
       let ltp = go gam lt in
       let rtp = go gam rt in
       let () = unify (ltp, NegArrow(rtp, Tvar v)) in
       Tvar v
    | Var db -> Tvar (List.nth gam db)
  in
  go [] tree

let rec tree_of_type tp = match tp with
  (* Eliminating the use of LITop -> "spos" for now *)
  | PosArrow (top, lt, rt) -> Bin ((match top with LITop -> "pos" | LIMid -> "pos"), tree_of_type lt, tree_of_type rt)
  | NegArrow (lt, rt) -> Bin ("neg", tree_of_type lt, tree_of_type rt)
  | Tvar {contents = (name, None)} -> Leaf name
  | Tvar {contents = (_, Some inst)} -> tree_of_type inst

(* ----------------------------------- *)
(* Tree Utilities *)
(* ----------------------------------- *)

let pairs_of_vars vs =
  let find_use x ics = fst (List.find (fun y -> snd y = x) ics) in
  let rec go ics = match ics with
    | [] -> []
    | ((i,  x)::tl) ->
       try (i, find_use x tl) :: go tl
       with Not_found -> go tl
  in
  go (List.mapi (fun x y -> (x, y)) vs)

let rec leafs_of_tree tree = match tree with
  | Leaf n -> [n]
  | Bin (_, lt, rt) -> leafs_of_tree lt @ leafs_of_tree rt
  | Un (_, bt) -> leafs_of_tree bt

let rec subtrees_of_tree tree = tree :: match tree with
  | Leaf n -> []
  | Bin (_, lt, rt) -> subtrees_of_tree lt @ subtrees_of_tree rt
  | Un (_, bt) -> subtrees_of_tree bt

let rec vertex_subtrees_of_tree tree =
  tree ::
    (match tree with
     | Bin ("lamv", lt, _) -> vertex_subtrees_of_tree lt
     | Bin ("lame", _, rt) -> vertex_subtrees_of_tree rt
     | Bin ("fuse", _, rt) -> vertex_subtrees_of_tree rt
     | Bin ("marker", _, rt) -> vertex_subtrees_of_tree rt
     | Bin ("marker2", _, rt) -> vertex_subtrees_of_tree rt
     | _ -> [])

let rec tree_map f tree = match tree with
  | Leaf n -> Leaf (f n)
  | Bin (name, lt, rt) -> Bin(name, tree_map f lt, tree_map f rt)
  | Un (name, bt) -> Un(name, tree_map f bt)

let rec findo f xs = match xs with
  | [] -> raise Not_found
  | h::tl -> match f h with Some s -> s | None -> findo f tl

(* ----------------------------------- *)
(* Conversion to Trinity *)
(* ----------------------------------- *)

type mapsort = MVert | MEdge

type 'a frontier = FLeft of 'a | FRight of 'a
type wire = WSubnorm | WAtom | WCoe

let frontierify_tree tree =
  let rec gosome tree k = go tree (Some k)
  and     go tree k = match tree with
    | Un (opr, bt) -> Un (opr, gosome bt (FLeft opr)) (* FLeft I guess ??? *)
    | Bin (opr, lt, rt) -> Bin (opr, gosome lt (FLeft opr), gosome rt (FRight opr))
    | Leaf data -> Leaf (data, k)
  in
  go tree None

type lindex = Lind of int

let number_leafs tree =
  let rec go n tree = match tree with
    | Bin (opr, lt, rt) ->
        let (lto, n1) = go n lt in
        let (rto, n2) = go n1 rt in
        (Bin(opr, lto, rto), n2)
    | Leaf data -> (Leaf (data, Lind n), n+1)
  in
  fst (go 0 tree)

let status_tree tp =
  let ttree = tree_of_type tp in
  let ntree = number_leafs ttree in
  let pairs = pairs_of_vars (leafs_of_tree ttree) in
  let find_partner (Lind n) =
    findo (fun (a, b) -> if      a = n then Some b
                         else if b = n then Some a
                         else None) pairs
  in
  let statuses = List.map (fun x -> match x with
                                    | Some (FLeft "neg") -> WSubnorm
                                    | Some (FRight "pos") -> WCoe
                                    | _ -> WAtom)
                          (List.map snd (leafs_of_tree (frontierify_tree ttree)))
  in
  let partner_status lind = List.nth statuses (find_partner lind) in
  tree_map (fun (name, lind) -> (name, partner_status lind)) ntree

let trin_of_type tp =
  let counter = ref 0 in
  let new_var(counter) =
    let c = !counter in
    let () = counter := c + 1 in
    Leaf (c, MVert)
  in
  let rec go_sub tree = match tree with
    | Leaf(name, _) -> Leaf(name, MEdge)
    | _ -> let v = new_var counter in Bin("lamv", go_norm tree v, v)
  and go_norm tree v = match tree with
    | Leaf(name, _) -> Bin("marker2", Leaf(name, MEdge), v)
    | Bin("pos", lt, rt) -> go_atom lt (go_norm rt v)
    | _ -> raise Not_found
  and go_atom tree v = match tree with
    (* XXX Now what I'm doing with this case and the go_norm Leaf case
       is trying to create two linked markers. *)
    | Leaf(name, WCoe) -> Bin("marker", Leaf(name, MEdge), v)
    | Leaf(name, WAtom) -> v
    | Leaf(name, WSubnorm) -> Bin("lame", Leaf(name, MEdge), v)
    | Bin("neg", lt, rt) -> Bin("fuse", go_sub lt, go_atom rt v)
    | _ -> raise Not_found
  in
  go_sub (status_tree tp)

(* ----------------------------------- *)
(* Tree Visualization *)
(* ----------------------------------- *)

(* Assign unique names to all variables, and homogenize the structure
   so that lam and app look like binary nodes of a tree, and variable
   occurrences look the same as variable bindings. *)
let tree_of_term term =
  (* x is the term being processed *)
  (* gam is the context, a list of globally distinct names for variables,
     whose position in gam is their debruijn index *)
  (* n is an incrementing counter to give distinct names to variables *)
  let rec go x gam n = match x with
    | Lam (top, body) ->
       let (bo, n1) = go body (n::gam) (n+1) in
       (Bin((match top with LITop -> "slam" | LIMid -> "lam"), Leaf n, bo), n1)
    | App (lt, rt) ->
       let (lo, n1) = go lt gam n in
       let (ro, n2) = go rt gam n1 in
       (Bin("app", lo, ro), n2)
    | Var db -> (Leaf (List.nth gam db), n)
  in
  let (out, _) = go term [] 0 in
  out

let rec json_of_tree x = match x with
  | Un (name, bt) ->
     `Assoc [
        "type", `String "un";
        "subtype", `String name;
        "B", json_of_tree bt;
      ]
  | Bin (name, lt, rt) ->
     `Assoc [
        "type", `String "bin";
        "subtype", `String name;
        "L", json_of_tree lt;
        "R", json_of_tree rt;
      ]
  | Leaf _ ->
     `Assoc [
        "type", `String "var";
      ]

let json_of_pairs cs = `List (List.map (fun (x, y) ->  `List [`Int x; `Int y]) cs)

let json_of_frontier fs =
  `List
   (List.map
      (fun fx -> match fx with
                 | Some(FLeft x) -> `List [`String "left"; `String x]
                 | Some(FRight x) -> `List [`String "right"; `String x]
                 | _ -> `Null) fs)

let (++) f g x = f(g(x))

let json_of_tree tree =
  `Assoc
   ((List.map (fun (k, f) -> (k, f tree))) [
        "tree", json_of_tree;
        "conn", json_of_pairs ++ pairs_of_vars ++ leafs_of_tree;
        "front", json_of_frontier ++ (List.map snd) ++ leafs_of_tree ++ frontierify_tree;
   ])

(* ----------------------------------- *)
(* Tree Stringification *)
(* ----------------------------------- *)

(* Given a 'balanced' list, where every element occurs exactly twice,
   return a function that maps every occurring element to its rank,
   where the first distinct element to appear has rank 0, the next has
   rank 1, etc.

   For example, list_normalizer ["a"; "b"; "d"; "b"; "a"; "c"; "c"; "d"] returns
   a function f such that
   f "a" = 0
   f "b" = 1
   f "d" = 2
   f "c" = 3
 *)
let list_normalizer xs =
  let rec go xs n mem = match xs with
    | [] -> mem
    | h::tl -> if List.exists (fun (k, _) -> k = h) mem
               then go tl n mem
               else go tl (n+1) ((h,n)::mem)
  in
  let mem = go xs 0 [] in
  fun k -> snd (List.find (fun ki -> fst ki = k) mem)

let normalize_tree tree =
  let leafs = leafs_of_tree tree in
  let leaf_normalizer = list_normalizer leafs in
  tree_map leaf_normalizer tree

let namer defaults numbered n =
  if n < List.length defaults
  then List.nth defaults n
  else numbered ^ string_of_int(n - List.length defaults)

let term_namer n = namer ["x"; "y"; "z"; "u"; "v"; "w"; "s"; "t"] "a" n
let type_namer n = namer ["A"; "B"; "C"; "D"; "E"; "F"; "G"] "X" n
let trinity_namer n = namer [] "t" n

let string_of_tree tree var_namer =
  let rec go t = match t with
    | Leaf s -> s
    | Bin(name, lt, rt) -> name ^ "(" ^ go lt ^ ", " ^ go rt ^ ")"
  in
  go (tree_map var_namer (normalize_tree tree))

let lambda = "/"
let slambda = "/"
let pos = " ->> "
let spos = " ->> "
let neg = " >-> "
(*
let lambda = "\\u03bb"
let slambda = "\\u039b"
let pos = " \\u21a0 "
let spos = " \\u27ff "
let neg = " \\u21a3 "
 *)

let string_of_term_tree tree  =
  let parenize b x = if b then "(" ^ x ^ ")" else x in
  let rec go t paren_arrow = match t with
    | Leaf s -> s
    | Bin("lam", lt, rt) -> parenize paren_arrow (lambda ^ go lt false ^ "." ^ go rt false)
    | Bin("slam", lt, rt) -> parenize paren_arrow (slambda ^ go lt false ^ "." ^ go rt false)
    | Bin("app", lt, rt) -> parenize paren_arrow (go lt false ^ " " ^ go rt true)
  in
  go (tree_map term_namer (normalize_tree tree)) false

let string_of_type_tree tree  =
  let parenize b x = if b then "(" ^ x ^ ")" else x in
  let rec go t paren_arrow = match t with
    | Leaf s -> s
    | Bin("pos", lt, rt) ->  parenize paren_arrow (go lt true ^ pos ^ go rt false)
    | Bin("spos", lt, rt) ->  parenize paren_arrow (go lt true ^ spos ^ go rt false)
    | Bin("neg", lt, rt) ->  parenize paren_arrow (go lt true ^ neg ^ go rt false)
  in
  go (tree_map type_namer (normalize_tree tree)) false

let string_of_trinity_tree tree  =
  let parenize x = "(" ^ x ^ ")" in
  let rec go t = match t with
    | Leaf s -> s
    | Bin("fuse", lt, rt) ->  parenize (go lt ^ " * " ^ go rt)
    | Bin("lame", lt, rt) ->  parenize (go lt ^ " V " ^ go rt)
    | Bin("lamv", lt, rt) ->  parenize (go lt ^ " E " ^ go rt)
    | Bin("marker", lt, rt) ->  parenize (go lt ^ " M " ^ go rt)
    | Bin("marker2", lt, rt) ->  parenize (go lt ^ " N " ^ go rt)
  in
  go (tree_map trinity_namer (normalize_tree tree))

(* ----------------------------------- *)
(* Local orientability conjecture *)
(* ----------------------------------- *)

(* Conjecture: a trinity term corresponds to a locally orientable map
   if each vertex has precisely one marker pair. *)

let count_markers tree =
  List.length (List.filter (fun st -> match st with
                                      | Bin ("marker", _, _) -> true
                                      | Bin ("marker2", _, _) -> true
                                      | _ -> false) (vertex_subtrees_of_tree tree))

let list_bins tree =
  List.flatten (List.map (fun st -> match st with
                                      | Bin (name, _, _) -> [name]
                                      | _ -> []) (vertex_subtrees_of_tree tree))

let locally_orientable tree =
  let lamvs = List.filter (fun st -> match st with
                                     | Bin("lamv", _, _) -> true
                                     | _ -> false) (subtrees_of_tree tree) in

  let counts = List.map count_markers lamvs in
  `Bool (List.for_all (fun x -> x = 2) counts)
  (* `List (List.map (fun x -> `Int x) counts) *)

let orientable tree =
  let lamvs = List.filter (fun st -> match st with
                                     | Bin("lamv", _, _) -> true
                                     | _ -> false) (subtrees_of_tree tree) in

  let bins = List.map list_bins lamvs in
  `Bool (List.for_all (fun x -> List.hd (List.tl (List.rev x)) = "marker") bins)
  (* `List (List.map (fun x -> `Int x) counts) *)


(* ----------------------------------- *)
(* Main program *)
(* ----------------------------------- *)

let enum_ordered = enumerator left_extend list_splits
let enum_linear = enumerator left_extend linear_splits

let data_of_term term =
  let term_tree = tree_of_term term in
  let tp = type_of_term term in
  let type_tree = tree_of_type tp in
  let trin_tree = trin_of_type tp in
  `Assoc[
     "term", json_of_tree term_tree;
     "type", json_of_tree type_tree;
     "trin", json_of_tree trin_tree;
     "term_string", `String (string_of_term_tree term_tree);
     "type_string", `String (string_of_type_tree type_tree);
     "trinity_string", `String (string_of_trinity_tree trin_tree);
     "locally_orientable", locally_orientable trin_tree;
     "orientable", orientable trin_tree;
   ]

let write() =
  let terms = enum_linear 4 [] in
  let json = `List (List.map data_of_term terms) in
  let json_string = to_string json in
  let oc = open_out "data.js"  in
  Printf.fprintf oc "var data = %s\n" json_string;
  close_out oc;
  let oc = open_out "data.json"  in
  Printf.fprintf oc "%s\n" json_string;
  close_out oc

let _ = write()


(* let term = List.nth (enum_linear 5 []) 5 *)
(* let ttree = tree_of_type (type_of_term term) *)
(* let ntree = number_leafs ttree *)
(* let pairs = pairs_of_vars (leafs_of_tree ttree) *)


(* let find_partner (Lind n) = *)
(*   findo (fun (a, b) -> if      a = n then Some b *)
(*                        else if b = n then Some a *)
(*                        else None) pairs *)

(* let statuses = List.map (fun x -> match x with *)
(*                                   | Some (FLeft "neg") -> WSubnorm *)
(*                                   | _ -> WAtom) *)
(*                         (List.map snd (leafs_of_tree (frontierify_tree ttree))) *)

(* let partner_status lind = List.nth statuses (find_partner lind) *)

(* let status_tree = tree_map (fun (name, lind) -> (name, partner_status lind)) ntree *)
