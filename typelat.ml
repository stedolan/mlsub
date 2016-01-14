type polarity = Pos | Neg

let polneg = function Pos -> Neg | Neg -> Pos
let polmul = function Pos -> (fun p -> p) | Neg -> polneg

let pol_flip f pol x y = match pol with Pos -> f x y | Neg -> f y x

(* FIXME *)
module SMap = Map.Make (struct type t = int let compare = compare end)

type 'a printer = Format.formatter -> 'a -> unit
let print_to_string (pr : 'a printer) (x : 'a) : string =
  let buf = Buffer.create 100 in
  let ppf = Format.formatter_of_buffer buf in
  Format.fprintf ppf "%a%!" pr x;
  Buffer.contents buf
  
  
module Components = struct
  type 'a t =
    | Func of (Location.set * 'a) list * (Location.set * 'a) SMap.t * unit SMap.t * (Location.set * 'a)
    | Object of (Location.set * 'a) SMap.t
    | List of Location.set * 'a
    | Base of Location.set * Symbol.t

  let locations = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> Location.join l r) pos 
         (SMap.fold (fun k (l, a) r -> Location.join l r) kwargs l)
    | Object o -> SMap.fold (fun _ (l, _) locs -> Location.join l locs) o Location.empty
    | List (l, _) -> l
    | Base (l, _) -> l

  let change_locations l' = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l', a)) pos, 
             SMap.map (fun (l, a) -> (l', a)) kwargs,
             reqs,
             (l', res))
    | Object o -> Object (SMap.map (fun (l, a) -> (l', a)) o)
    | List (l, a) -> List (l', a)
    | Base (l, s) -> Base (l', s)

  let pmap f pol = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l, f (polneg pol) a)) pos,
             SMap.map (fun (l, a) -> (l, f (polneg pol) a)) kwargs,
             reqs,
             (l, f pol res))
    | Object o -> Object (SMap.map (fun (l, x) -> (l, f pol x)) o)
    | List (l, a) -> List (l, f pol a)
    | Base (l, s) -> Base (l, s)

  let pfold f pol t x = match t with
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> f (polneg pol) a r) pos
         (SMap.fold (fun k (l, a) r -> f (polneg pol) a r) kwargs
            (f pol res x))

    | Object o -> SMap.fold (fun k (l, t) x -> f pol t x) o x
    | List (l, a) -> f pol a x
    | Base (l, s) -> x

  let cmp_component (type a) (type b) (x : a t) (y : b t) = match x, y with
    | Func (pos, _, _, _), Func (pos', _, _, _) -> List.length pos = List.length pos'
    | Object _, Object _ -> true
    | List _, List _ -> true
    | Base (l, s), Base (l', s') -> s = s'
    | _, _ -> false

  let join pol f x y = match x, y, pol with
    | Func (pos, kwargs, reqs, (l, res)), Func (pos', kwargs', reqs', (l', res')), pol ->
       let kw_merge k x y = match pol, x, y with
         | pol, Some (l, a), Some (l', a') -> Some
            (Location.join l l',
             f (polneg pol) a a')

         (* negatively, take union of keyword arguments *)
         | Neg, (Some _ as arg), None
         | Neg, None, (Some _ as arg) -> arg

         (* positively, take intersection of keyword arguments *)
         | Pos, Some _, None
         | Pos, None, Some _ -> None

         | pol, None, None -> None in
       let req_merge k x y = match pol, x, y with
         | _, Some (), Some () -> Some ()
         | _, None, None -> None

         (* negatively, take intersection of required arguments *)
         | Neg, Some (), None
         | Neg, None, Some () -> None

         (* positively, take union of required arguments *)
         | Pos, Some (), None
         | Pos, None, Some () -> Some () in
       Func (List.map2 (fun (l, a) (l', a') -> (Location.join l l', f (polneg pol) a a')) pos pos',
             SMap.merge kw_merge kwargs kwargs',
             SMap.merge req_merge reqs reqs',
             (Location.join l l', f pol res res'))

    | Object x, Object y, Pos ->
       Object (SMap.merge (fun k x y ->
         match x, y with (* lub takes intersection of fields *)
         | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Pos x y)
         | _, _ -> None) x y)
    | Object x, Object y, Neg ->
       Object (SMap.merge (fun k x y ->
         match x, y with (* glb takes union of fields *)
         | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Neg x y)
         | Some a, None
         | None, Some a -> Some a
         | None, None -> None) x y)

    | List (l, a), List (l', a'), pol ->
       List (Location.join l l', f pol a a')

    | Base (l, s), Base (l', s'), pol when s = s' ->
       Base (Location.join l l', s)

    | _, _, _ ->
       assert (cmp_component x y); assert false

  let lte (type a) (type b) f (x : a t) (y : b t) = match x, y with
    | Func (pos, kwargs, reqs, (l, res)), Func (pos', kwargs', reqs', (l', res')) when cmp_component x y ->
       let kw_cmp r =
         SMap.fold (fun k (l', t') r ->
           if SMap.mem k kwargs then
             let (l, t) = SMap.find k kwargs in
             f Neg t t' @ r
           else [Error.Conflict (locations x, "keyword", l', Symbol.to_string k)] @ r) kwargs' r in
       let req_cmp r =
         SMap.fold (fun k () r ->
           if SMap.mem k reqs' then r else
             [Error.Conflict (locations x, "required+", locations y, Symbol.to_string k)] @ r) reqs r in
       f Pos res res' |> req_cmp |> kw_cmp |>
           List.fold_right2 (fun (l, x) (l, y) r -> f Neg x y @ r) pos pos'

    | Object ox, Object oy -> 
       SMap.fold (fun k (yl, yk) r -> 
         if SMap.mem k ox then
           let (xl, xk) = SMap.find k ox in
           f Pos xk yk @ r
         else [Error.Conflict (locations x, "{}", yl, Symbol.to_string k)] @ r) oy []

    | List (l, a), List (l', a') ->
       f Pos a a'

    | Base (l, s), Base (l', s') when s = s' ->
       []

    (* error cases *)
    | x, y ->
       let name = function
       | Func _ -> "function"
       | Object _ -> "object"
       | List _ -> "list"
       | Base (_, s) -> Symbol.to_string s in
       [Error.Conflict (locations x, name x, locations y, name y)]

  let list_fields = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.mapi (fun i (l, a) -> (string_of_int i, a)) pos @
         (SMap.bindings kwargs |> List.map (fun (k, (l, a)) -> (Symbol.to_string k, a))) @
         ["res", res]
    | Object o -> List.map (fun (k, (_, v)) -> (Symbol.to_string k, v)) (SMap.bindings o)
    | List (l, a) -> ["e", a]
    | Base (l, s) -> []

  let print pr pol ppf = function
    | Func (pos, kwargs, reqs, (l, res)) ->
       let args = List.map (fun (l, a) -> (None, Some a)) pos @
         (SMap.merge (fun k arg req -> match arg, req with
          | Some (l, a), None -> Some (Some (Symbol.to_string k ^ "?"), Some a)
          | Some (l, a), Some () -> Some (Some (Symbol.to_string k), Some a)
          | None, Some () -> Some (Some (Symbol.to_string k), None)
          | None, None -> None) kwargs reqs |> SMap.bindings |> List.map (fun (a, b) -> b)) in
       let pr_arg ppf = function
         | None, None -> ()
         | None, Some t -> Format.fprintf ppf "%a" (pr (polneg pol)) t
         | Some name, Some t -> Format.fprintf ppf "%s : %a" name (pr (polneg pol)) t
         | Some name, None -> Format.fprintf ppf "%s : <err>" name in
       let comma ppf () = Format.fprintf ppf ",@ " in
       Format.fprintf ppf "(%a) -> %a"
         (Format.pp_print_list ~pp_sep:comma pr_arg) args
         (pr pol) res
    | Object _ as o ->
       let rec pfield ppf = function
         | [] -> ()
         | [f, x] ->
            Format.fprintf ppf "%s :@ %a" f (pr pol) x
         | (f, x) :: xs ->
            Format.fprintf ppf "%s :@ %a,@ %a" f (pr pol) x pfield xs in
       Format.fprintf ppf "{%a}" pfield (list_fields o)
    | List (l, a) ->
       Format.fprintf ppf "List[%a]" (pr pol) a
    | Base (l, s) ->
       Format.fprintf ppf "%s" (Symbol.to_string s)
end

module type TYPES = sig
    type 'a t
    val lift : 'a Components.t -> 'a t
    val join : polarity -> (polarity -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    val join_ident : 'a t

    val lte_pn : ('a -> 'a -> Error.t list) -> 'a t -> 'a t -> Error.t list
    val lte_np : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val subs : polarity -> (polarity -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

    val pmap : (polarity -> 'a -> 'b) -> polarity -> 'a t -> 'b t
    val pfold : (polarity -> 'a -> 'r -> 'r) -> polarity -> 'a t -> 'r -> 'r
    val iter : (polarity -> 'a -> unit) -> polarity -> 'a t -> unit

    val print : (polarity -> 'a printer) -> polarity -> 'a t printer
    val list_fields : 'a t -> (string * 'a) list

    val change_locations : Location.set -> 'a t -> 'a t
  end

module TypeLat : TYPES = struct
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

  let print pr pol ppf = function
    | [] -> Format.fprintf ppf "%s" (match pol with Pos -> "Bot" | Neg -> "Top")
    | ty ->
       let pp_sep ppf () = Format.fprintf ppf "@ %s@ " (match pol with Pos -> "|" | Neg -> "&") in
       Format.pp_print_list ~pp_sep (Components.print pr pol) ppf ty

  let change_locations l = List.map (Components.change_locations l)
end
