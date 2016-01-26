type polarity = Pos | Neg

let polneg = function Pos -> Neg | Neg -> Pos
let polmul = function Pos -> (fun p -> p) | Neg -> polneg

let pol_flip f pol x y = match pol with Pos -> f x y | Neg -> f y x

type 'a printer = Format.formatter -> 'a -> unit


(* FIXME *)
module SMap = Map.Make (struct type t = int let compare = compare end)
  
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


let ty_list e loc = Components.List (Location.one loc, e loc)
let ty_fun pos kwargs res loc = Components.Func (
  List.map (fun a -> (Location.one loc, a loc)) pos,
  SMap.map (fun (a, req) -> (Location.one loc, a loc)) kwargs,
  SMap.filter (fun k (a, req) -> req) kwargs |> SMap.map (fun _ -> ()),
  (Location.one loc, res loc))
let ty_obj o loc = Components.Object (SMap.map (fun x -> (Location.one loc, x loc)) o)
let ty_base s loc = Components.Base (Location.one loc, s)
