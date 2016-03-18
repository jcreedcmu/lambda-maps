#require "yojson";;
open Yojson;;

type term = Var of int | Lam of term | App of term * term

type 'a tree = Bin of string * 'a tree * 'a tree | Leaf of 'a

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

let enumerator var_extend var_splits =
  let rec enum_normal lams free  =
    let lamcase = if lams = 0
                  then []
                  else List.map (fun x -> Lam x) (enum_normal (lams-1) (var_extend free))
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
  enum_normal

let right_extend free =
  List.map (fun x -> x + 1) free @ [0]

let left_extend free =
  0 :: List.map (fun x -> x + 1) free

(* ----------------------------------- *)
(* Type Inference *)
(* ----------------------------------- *)

type tp =
  PosArrow of tp * tp
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
    | Lam body ->
       let v = new_tvar(counter) in
       PosArrow (Tvar v, go (v::gam) body)
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
  | PosArrow (lt, rt) -> Bin ("pos", tree_of_type lt, tree_of_type rt)
  | NegArrow (lt, rt) -> Bin ("neg", tree_of_type lt, tree_of_type rt)
  | Tvar {contents = (name, None)} -> Leaf name
  | Tvar {contents = (_, Some inst)} -> tree_of_type inst

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
    | Lam body ->
       let (bo, n1) = go body (n::gam) (n+1) in
       (Bin("lam", Leaf n, bo), n1)
    | App (lt, rt) ->
       let (lo, n1) = go lt gam n in
       let (ro, n2) = go rt gam n1 in
       (Bin("app", lo, ro), n2)
    | Var db -> (Leaf (List.nth gam db), n)
  in
  let (out, _) = go term [] 0 in
  out

let rec leafs_of_tree tree = match tree with
  | Leaf n -> [n]
  | Bin (_, lt, rt) -> leafs_of_tree lt @ leafs_of_tree rt

let rec tree_map f tree = match tree with
  | Leaf n -> Leaf (f n)
  | Bin (name, lt, rt) -> Bin(name, tree_map f lt, tree_map f rt)


let rec json_of_tree x = match x with
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

let pairs_of_vars vs =
  let find_use x ics = fst (List.find (fun y -> snd y = x) ics) in
  let rec go ics = match ics with
    | [] -> []
    | ((i,  x)::tl) ->
       try (i, find_use x tl) :: go tl
       with Not_found -> go tl
  in
  go (List.mapi (fun x y -> (x, y)) vs)

let json_of_pairs cs = `List (List.map (fun (x, y) ->  `List [`Int x; `Int y]) cs)

let json_of_tree tree =
  `Assoc [
     "tree", json_of_tree tree;
     "conn", json_of_pairs (pairs_of_vars (leafs_of_tree tree));
   ]

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

let string_of_tree tree var_namer =
  let rec go t = match t with
    | Leaf s -> s
    | Bin(name, lt, rt) -> name ^ "(" ^ go lt ^ ", " ^ go rt ^ ")"
  in
  go (tree_map var_namer (normalize_tree tree))

let string_of_term_tree tree  =
  let parenize b x = if b then "(" ^ x ^ ")" else x in
  let rec go t paren_arrow = match t with
    | Leaf s -> s
    | Bin("lam", lt, rt) -> parenize paren_arrow ("\\u03bb" ^ go lt false ^ "." ^ go rt false)
    | Bin("app", lt, rt) -> parenize paren_arrow (go lt false ^ " " ^ go rt true)
  in
  go (tree_map term_namer (normalize_tree tree)) false

let string_of_type_tree tree  =
  let parenize b x = if b then "(" ^ x ^ ")" else x in
  let rec go t paren_arrow = match t with
    | Leaf s -> s
    | Bin("pos", lt, rt) ->  parenize paren_arrow (go lt true ^ " \\u21a0 " ^ go rt false)
    | Bin("neg", lt, rt) ->  parenize paren_arrow (go lt true ^ " \\u21a3 " ^ go rt false)
  in
  go (tree_map type_namer (normalize_tree tree)) false

(* ----------------------------------- *)
(* Main program *)
(* ----------------------------------- *)

let enum_ordered = enumerator left_extend list_splits
let enum_linear = enumerator left_extend linear_splits

let (++) f g x = f(g(x))

let data_of_term term =
  let term_tree = tree_of_term term in
  let type_tree = tree_of_type (type_of_term term) in
  `Assoc[
     "term", json_of_tree term_tree;
     "type", json_of_tree type_tree;
     "term_string", `String (string_of_term_tree term_tree);
     "type_string", `String (string_of_type_tree type_tree);
   ]

let write() =
  let terms = enum_ordered 4 [] in
  let json = `List (List.map data_of_term terms) in
  let json_string = to_string json in
  let oc = open_out "data.js"  in
  Printf.fprintf oc "var data = %s\n" json_string;
  close_out oc

let _ = write()
