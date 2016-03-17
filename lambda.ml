type term = Var of int | Lam of term | App of term * term

let splits n f =
  let rec go m = if m < 0
                 then []
                 else f (m, (n-m)) @ go (m-1)
  in
  go n

let rec cross a b = match a with
  | [] -> []
  | h::tl -> List.map (fun bx -> (h, bx)) b @ cross tl b

let rec enum_ordered_normal lams free =
  let lamcase = if lams = 0
                then []
                else List.map (fun x -> Lam x) (enum_ordered_normal (lams-1) (free+1))
  in lamcase @ enum_ordered_atomic lams free
and enum_ordered_atomic lams free = match (lams, free) with
  | (0,1) -> [Var 0]
  | (_,_) -> let branches =
               splits lams (fun (lams1, lams2) ->
                        splits free (fun (free1, free2) ->
                                 if (free1 = 0) || (free2 = 0 && lams2 = 0)
                                 then []
                                 else cross (enum_ordered_atomic lams1 free1)
                                            (enum_ordered_normal lams2 free2))) in
             List.map (fun (x, y) -> App (x, y)) branches
