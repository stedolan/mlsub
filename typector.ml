open Variance

type 'a printer = Format.formatter -> 'a -> unit

module SMap = Symbol.Map

(*
  | TNamed (v, args) -> 
     let print_arg ppf = function
       | APos t -> fprintf ppf "+%a" print_typeterm t
       | ANeg t -> fprintf ppf "-%a" print_typeterm t
       | AUnspec t -> fprintf ppf "%a" print_typeterm t
       | ANegPos (s, t) -> fprintf ppf "-%a +%a" print_typeterm s print_typeterm t in
     let comma ppf () = Format.fprintf ppf ",@ " in
     fprintf ppf "%s[%a]" (string_of_var v) (Format.pp_print_list ~pp_sep:comma print_arg) args
*)

type stamp = int


  
module Components = struct
  type +'a t =
    | Func of (Location.set * 'a) list * (Location.set * 'a) SMap.t * unit SMap.t * (Location.set * 'a)
    | Object of (Location.set * 'a) SMap.t
    | List of Location.set * 'a
    | Base of Location.set * stamp * typedef

  and +'a tybody =
    | BParam of 'a
    | BCons of 'a tybody t

  and typedef =
    | TAlias of variance SMap.t * Symbol.t tybody
    | TOpaque of variance SMap.t


  let locations = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> Location.join l r) pos 
         (SMap.fold (fun k (l, a) r -> Location.join l r) kwargs l)
    | Object o -> SMap.fold (fun _ (l, _) locs -> Location.join l locs) o Location.empty
    | List (l, _) -> l
    | Base (l, _, _) -> l

  let change_locations l' = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l', a)) pos, 
             SMap.map (fun (l, a) -> (l', a)) kwargs,
             reqs,
             (l', res))
    | Object o -> Object (SMap.map (fun (l, a) -> (l', a)) o)
    | List (l, a) -> List (l', a)
    | Base (l, s, td) -> Base (l', s, td)

  let pmap f pol = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l, f (polneg pol) a)) pos,
             SMap.map (fun (l, a) -> (l, f (polneg pol) a)) kwargs,
             reqs,
             (l, f pol res))
    | Object o -> Object (SMap.map (fun (l, x) -> (l, f pol x)) o)
    | List (l, a) -> List (l, f pol a)
    | Base (l, s, td) -> Base (l, s, td)

  let pfold f pol t x = match t with
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> f (polneg pol) a r) pos
         (SMap.fold (fun k (l, a) r -> f (polneg pol) a r) kwargs
            (f pol res x))

    | Object o -> SMap.fold (fun k (l, t) x -> f pol t x) o x
    | List (l, a) -> f pol a x
    | Base (l, s, td) -> x

  let cmp_component (type a) (type b) (x : a t) (y : b t) = match x, y with
    | Func (pos, _, _, _), Func (pos', _, _, _) -> List.length pos = List.length pos'
    | Object _, Object _ -> true
    | List _, List _ -> true
    | Base (l, s, td), Base (l', s', td') -> s = s'
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

    | Base (l, s, td), Base (l', s', td'), pol when s = s' ->
       Base (Location.join l l', s, td)

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

    | Base (l, s, td), Base (l', s', td') when s = s' ->
       []

    (* error cases *)
    | x, y ->
       let name = function
       | Func _ -> "function"
       | Object _ -> "object"
       | List _ -> "list"
       | Base (_, s, td) -> "base" in (* FIXME *)
       [Error.Conflict (locations x, name x, locations y, name y)]

  let list_fields = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.mapi (fun i (l, a) -> (string_of_int i, a)) pos @
         (SMap.bindings kwargs |> List.map (fun (k, (l, a)) -> (Symbol.to_string k, a))) @
         ["res", res]
    | Object o -> List.map (fun (k, (_, v)) -> (Symbol.to_string k, v)) (SMap.bindings o)
    | List (l, a) -> ["e", a]
    | Base (l, s, td) -> []
end



type tyvar = Symbol.t

type typaram =
| TParam of Variance.variance option * Symbol.t

type tyarg =
| APos of typeterm
| ANeg of typeterm
| AUnspec of typeterm
| ANegPos of typeterm * typeterm

and typeterm =
| TZero of Variance.polarity
| TNamed of tyvar
| TCons of typeterm Components.t
| TAdd of Variance.polarity * typeterm * typeterm
| TRec of tyvar * typeterm


module StampMap = Map.Make (struct type t = stamp let compare = compare end)

type +'a tybody = 'a Components.tybody =
 | BParam of 'a
 | BCons of 'a tybody Components.t

open Components

type context = {
  next_stamp : stamp;
  by_name : (stamp * typedef) SMap.t; (* FIXME allow outer *)
  by_stamp : (Symbol.t * typedef) StampMap.t
}

let builtin_stamp : stamp = 0
let empty_context : context = { next_stamp = 1; by_name = SMap.empty; by_stamp = StampMap.empty }


let add_to_context err ctx name ty =
  if SMap.mem name ctx.by_name then
    (* FIXME: shadowing and outer *)
    failwith "reused name"
  else
    let stamp = ctx.next_stamp in
    { next_stamp = stamp + 1;
      by_name = SMap.add name (stamp, ty) ctx.by_name;
      by_stamp = StampMap.add stamp (name, ty) ctx.by_stamp }

let find_by_name ctx name =
  match SMap.find name ctx.by_name with
  | (n, _) -> Some n
  | exception Not_found -> None

let name_of_stamp ctx stamp =
  match StampMap.find stamp ctx.by_stamp with
  | (n, _) -> n
  | exception Not_found -> failwith "unbound stamp"


let printp paren ppf fmt = let open Format in
  let openbox ppf = if paren then fprintf ppf "@[(" else fprintf ppf "@[" in
  let closebox ppf = if paren then fprintf ppf "@])" else fprintf ppf "@]" in
  openbox ppf;
  kfprintf closebox ppf fmt

let print_comp ctx pr pol ppf = let open Components in function
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
  | Base (l, s, td) ->
     Format.fprintf ppf "%s" (Symbol.to_string (name_of_stamp ctx s))

let rec print_typeterm ctx ppf = let open Format in function
  | TZero Pos -> fprintf ppf "nothing"
  | TZero Neg -> fprintf ppf "any"
  | TNamed v -> fprintf ppf "%s" (Symbol.to_string v)
  | TCons cons ->
     fprintf ppf "@[%a@]" (print_comp ctx (fun pol -> print_typeterm ctx) Pos) cons
  | TAdd (p, t1, t2) -> 
    let op = match p with Pos -> "|" | Neg -> "&" in
    fprintf ppf "@[%a %s@ %a@]" (print_typeterm ctx) t1 op (print_typeterm ctx) t2
  | TRec (v, t) ->
    fprintf ppf "rec %s = %a" (Symbol.to_string v) (print_typeterm ctx) t



let ty_list e loc = Components.List (Location.one loc, e loc)
let ty_fun pos kwargs res loc = Components.Func (
  List.map (fun a -> (Location.one loc, a loc)) pos,
  SMap.map (fun (a, req) -> (Location.one loc, a loc)) kwargs,
  SMap.filter (fun k (a, req) -> req) kwargs |> SMap.map (fun _ -> ()),
  (Location.one loc, res loc))
let ty_obj o loc = Components.Object (SMap.map (fun x -> (Location.one loc, x loc)) o)
let ty_obj_l o loc =
  let o = List.fold_left (fun o (v, t) -> SMap.add v t o) SMap.empty o in
  ty_obj o loc
let ty_base ctx s loc =
(*  Format.printf "Context has %d/%d elems\n%!" (SMap.cardinal ctx.by_name) (StampMap.cardinal ctx.by_stamp);
  StampMap.iter (fun k (n, _) -> Format.printf "%d = %s\n" k (Symbol.to_string n)) ctx.by_stamp; *)
  match StampMap.find s ctx.by_stamp with
  | (name, td) -> Components.Base (Location.one loc, s, td)
  | exception Not_found -> failwith ("Unknown type with stamp " ^ string_of_int s)


let add_type_alias err name param_list term ctx =
  let rec mk_params s = function
    | [] -> s
    | TParam (v, p) :: ps ->
       mk_params (if SMap.mem p s then failwith "duplicate param" else SMap.add p v s) ps in
  let params = mk_params SMap.empty param_list in
  let rec inferred_variances = ref (SMap.map (fun _ -> VNone) params) in
  let use param pol =
    inferred_variances := 
      SMap.add param (vjoin 
        (SMap.find param !inferred_variances)
        (variance_of_pol pol)) !inferred_variances in

  let rec check pol = function
    | TNamed t when SMap.mem t params ->
       (use t pol; BParam t)
    | TNamed t ->
       (match find_by_name ctx t with
       | Some s -> BCons (ty_base ctx s Location.internal)
       | None -> failwith "unknown type")
    | TCons cons -> BCons (Components.pmap check pol cons) 
    | TZero _ -> failwith "nzero"
    | TAdd _ -> failwith "nadd"
    | TRec _ -> failwith "nrec" in

  let param_variances = SMap.merge (fun p asc infer -> match asc, infer with
    | None, _ | _, None -> assert false (* maps have same keys *)
    | Some (Some asc), Some infer -> assert (vlte infer asc); Some asc
    | Some None, Some infer -> Some infer) params !inferred_variances in

  add_to_context err ctx name (TAlias (param_variances, check Pos term))

let add_opaque_type err name param_list ctx =
  let rec check_params s = function
    | [] -> s
    | TParam (v, p) :: ps ->
       if SMap.mem p s then (failwith "duplicate param"; check_params s ps) else
         let s' = match v with Some v -> SMap.add p v s | None -> failwith "variance required"; s in
         check_params s' ps in
  add_to_context err ctx name (TOpaque (check_params SMap.empty param_list))


let get_stamp = function
  | Components.Base (_, s, TAlias _) -> s
  | _ -> builtin_stamp

let rec expand p = function
| BParam _ -> failwith "type alias parameters unsupported"
| BCons c -> BCons (pmap expand p c)

let expand_alias = function
  | Components.Base (_, s, TAlias (params, body)) ->
     (match body with
     | BParam _ -> failwith "Non-contractive type alias"
     | BCons c -> pmap expand Pos c)
  | _ -> failwith "Attempt to expand a type which is not an alias"
