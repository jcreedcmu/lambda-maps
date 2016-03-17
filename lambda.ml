#require "yojson";;
open Yojson;;

type term = Var of int | Lam of term | App of term * term

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

let rec term_to_tree_json x = match x with
  | Lam body ->
     `Assoc [
        "type", `String "lam";
        "B", term_to_tree_json body;
      ]
  | App (lt, rt) ->
     `Assoc [
        "type", `String "app";
        "L", term_to_tree_json lt;
        "R", term_to_tree_json rt;
      ]
  | Var _ ->
     `Assoc [
        "type", `String "var";
      ]


type conn = Bind of int | Use of int


let rec term_to_conns_ctr gam n x  = match x with
  | Lam body ->
     let (conns, n1) = term_to_conns_ctr (n::gam) (n+1) body in
     (Bind n :: conns, n1)
  | App (lt, rt) ->
     let (conns1, n1) = term_to_conns_ctr gam n lt in
     let (conns2, n2) = term_to_conns_ctr gam n1 rt in
     (conns1 @ conns2, n2)
  | Var db -> ([Use(List.nth gam db)], n)
let term_to_conns x = let (conns, _) = term_to_conns_ctr [] 0 x in conns

let conns_to_pairs cs =
  let find_use x ics = fst (List.find (fun y -> snd y = Use x) ics) in
  let rec go ics = match ics with
    | [] -> []
    | ((i, Bind x)::tl) -> (i, find_use x tl) :: go tl
    | ((i, Use x)::tl) -> go tl in
  go (List.mapi (fun x y -> (x, y)) cs)

let pairs_to_json cs = `List (List.map (fun (x, y) ->  `List [`Int x; `Int y]) cs)

let term_to_conn_json x = `Null

let term_to_json x = `Assoc [
                        "tree", term_to_tree_json x;
                        "conn", pairs_to_json (conns_to_pairs (term_to_conns x));
                      ]

let enum_ordered = enumerator left_extend list_splits
let enum_linear = enumerator left_extend linear_splits

let _ = print_string (to_string (`List (List.map term_to_json (enum_linear 3 []))))
