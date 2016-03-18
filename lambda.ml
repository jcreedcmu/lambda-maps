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
(* Term Visualization *)
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

let json_of_term term =
  let tree = tree_of_term term in
  `Assoc [
     "tree", json_of_tree tree;
     "conn", json_of_pairs (pairs_of_vars (leafs_of_tree tree));
   ]

let enum_ordered = enumerator left_extend list_splits
let enum_linear = enumerator left_extend linear_splits

(* let x = leafs_of_tree(tree_of_term(List.nth (enum_linear 3 []) 15))*)

let write() =
  let json_string = to_string (`List (List.map json_of_term (enum_linear 3 []))) in
  let oc = open_out "data.js"  in
  Printf.fprintf oc "var data = %s\n" json_string;
  close_out oc

let _ = write()
