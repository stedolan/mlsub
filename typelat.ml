open Variance
open Typector
open Exp

let rec ty_add p ts = ts
  |> List.filter (function
     | TZero p' when p = p' -> false
     | _ -> true)
  |> function
    | [] -> TZero p
    | [t] -> t
    | (t :: ts) -> TAdd (p, t, ty_add p ts)

module TypeLat = struct
  type 'a t = 'a Components.t list
  let lift t = [t]
  let pmap f pol ty = List.map (Components.pmap f pol) ty
  let rec pfold f pol ty x = match ty with
    | [] -> x
    | t :: ts -> Components.pfold f pol t (pfold f pol ts x)

  let iter f p x = pfold (fun pol x r -> f pol x) p x ()

  let rec join pol f xs ys = match xs with
    | [] -> ys
    | x :: xs ->
       match List.partition (Components.cmp_component x) ys with
       | [], ys -> x :: join pol f xs ys
       | [y], ys -> Components.join pol f x y :: join pol f xs ys
       | y1 :: y2 :: _, _ -> failwith "two terms in same component"

  let join_ident = []

  let lte_pn f xs ys =
    (* lub X <= glb Y *)
    (* i.e. forall i,j, Xi <= Yj *)
    List.fold_right (fun x rs -> 
      List.fold_right (fun y rs -> 
        Components.lte (pol_flip f) x y @ rs) ys rs) xs []

  let lte_np f xs ys =
    (* glb X <= lub Y *)
    (* i.e. exists i,j, Xi <= Yj *)
    List.exists (fun x -> List.exists (fun y ->
      Components.lte (fun p x y -> if pol_flip f p x y then [] else [Error.excuse]) x y = []) ys) xs

  let rec subs pol f xs ys =
    (* lub X <= lub Y or glb X >= glb Y *)
    match xs with
    | [] -> true
    | x :: xs -> match List.partition (Components.cmp_component x) ys with
      | [], ys -> false
      | [y], ys ->
         (match pol with
         | Pos -> Components.lte (fun p x y -> if f p x y then [] else [Error.excuse]) x y = []
         | Neg -> Components.lte (fun p y x -> if f (polneg p) x y then [] else [Error.excuse]) y x = [])
         && subs pol f xs ys
      | y1 :: y2 :: _, _ -> failwith "two terms in same component"

  let list_fields x =
    x |> List.map Components.list_fields |> List.concat

  let to_typeterm pol x =
    ty_add pol (List.map (fun t -> TCons t) x)

  let print pr pol ppf = function
    | [] -> Format.fprintf ppf "%s" (match pol with Pos -> "Bot" | Neg -> "Top")
    | ty ->
       let pp_sep ppf () = Format.fprintf ppf "@ %s@ " (match pol with Pos -> "|" | Neg -> "&") in
       Format.pp_print_list ~pp_sep (Components.print pr pol) ppf ty

  let change_locations l = List.map (Components.change_locations l)
end



  
