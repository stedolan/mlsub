open Variance

type conflict_reason =
| Wrong_arity of int * int
| Unknown_kwarg of Symbol.t
| Missing_req_kwarg of Symbol.t
| Missing_field of Symbol.t
| Missing_case of Symbol.t option
| Incompatible_type of [`Func | `Obj | `Base of Symbol.t] * [`Func | `Obj | `Base of Symbol.t]

module SMap = Symbol.Map

type stamp = int


type +'a tyarg =
| APos of 'a
| ANeg of 'a
| ANegPos of 'a * 'a
| ANone

type conflict =
  Location.set * Location.set * conflict_reason


module Components = struct
  type +'a objfields = (Location.set * 'a) SMap.t
  type +'a t =
    | Func of (Location.set * 'a) list * (Location.set * 'a) SMap.t * unit SMap.t * (Location.set * 'a)
    | Object of 'a objfields SMap.t * 'a objfields option
    | Base of Location.set * stamp * typedef * 'a tyarg list

  and +'a tybody =
    | BParam of 'a
    | BCons of 'a tybody t

  and typedef =
    | TAlias of Symbol.t * (variance * Symbol.t option) array * int tybody
    | TOpaque of Symbol.t * (variance * Symbol.t option) array


  let locations = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> Location.join l r) pos 
         (SMap.fold (fun k (l, a) r -> Location.join l r) kwargs l)
    | Object (tagged, untagged) -> 
       let locfields _ o fs =
         SMap.fold (fun _ (l, _) locs -> Location.join l locs) o fs in
       SMap.fold locfields tagged (match untagged with
       | Some o -> locfields () o Location.empty
       | None -> Location.empty)
    | Base (l, _, _, ts) -> l

  let change_locations l' = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l', a)) pos, 
             SMap.map (fun (l, a) -> (l', a)) kwargs,
             reqs,
             (l', res))
    | Object (tagged, untagged) -> 
       let mapfields o = SMap.map (fun (l, a) -> (l', a)) o in
       Object (SMap.map mapfields tagged, 
               match untagged with Some o -> Some (mapfields o) | None -> None)
    | Base (l, s, td, args) -> Base (l', s, td, args)

  let pmap f pol = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l, f (polneg pol) a)) pos,
             SMap.map (fun (l, a) -> (l, f (polneg pol) a)) kwargs,
             reqs,
             (l, f pol res))
    | Object (tagged, untagged) -> 
       let mapobj o = SMap.map (fun (l, x) -> (l, f pol x)) o in
       Object (SMap.map mapobj tagged,
               match untagged with Some o -> Some (mapobj o) | None -> None)
    | Base (l, s, td, args) -> Base (l, s, td, List.map (function
      | APos t -> APos (f pol t)
      | ANeg t -> ANeg (f (polneg pol) t)
      | ANegPos (s, t) -> ANegPos (f (polneg pol) s, f pol t)
      | ANone -> ANone) args)

  let pfold f pol t x = match t with
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> f (polneg pol) a r) pos
         (SMap.fold (fun k (l, a) r -> f (polneg pol) a r) kwargs
            (f pol res x))

    | Object (tagged, untagged) -> 
       let foldobj _ o x = SMap.fold (fun k (l, t) x -> f pol t x) o x in
       SMap.fold foldobj tagged (match untagged with
       | Some o -> foldobj () o x
       | None -> x)
    | Base (l, s, td, args) -> List.fold_right (fun arg x -> match arg with
      | APos t -> f pol t x
      | ANeg t -> f (polneg pol) t x
      | ANegPos (s, t) -> f (polneg pol) s (f pol t x)
      | ANone -> x) args x

  let cmp_component (type a) (type b) (x : a t) (y : b t) = match x, y with
    | Func (pos, _, _, _), Func (pos', _, _, _) -> List.length pos = List.length pos'
    | Object _, Object _ -> true
    | Base (l, s, td, args), Base (l', s', td', args') -> s = s'
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

    | Object (xtagged, xuntagged), Object (ytagged, yuntagged), Pos ->
       let join_objs x y = SMap.merge (fun k x y ->
         match x, y with (* lub takes intersection of fields *)
         | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Pos x y)
         | _, _ -> None) x y in
       let tagged = SMap.merge (fun k x y ->
         match x, y with (* lub takes union of tags *)
         | Some x, Some y -> Some (join_objs x y)
         | None, a | a, None -> a) xtagged ytagged in
       let untagged = match xuntagged, yuntagged with
         | Some x, Some y -> Some (join_objs x y)
         | None, a | a, None -> a in
       Object (tagged, untagged)

    | Object (xtagged, xuntagged), Object (ytagged, yuntagged), Neg ->
       let meet_objs x y = SMap.merge (fun k x y ->
         match x, y with (* glb takes union of fields *)
         | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Neg x y)
         | Some a, None
         | None, Some a -> Some a
         | None, None -> None) x y in
       let tagged = SMap.merge (fun k x y ->
         match (x, xuntagged), (y, yuntagged) with (* glb takes intersection of tags *)
         | ((Some x, _) | (None, Some x)),
           ((Some y, _) | (None, Some y)) ->
            Some (meet_objs x y)
         | ((None, None), _) | (_, (None, None)) -> None) xtagged ytagged in
       let untagged = match xuntagged, yuntagged with
         | None, _ | _, None -> None
         | Some x, Some y -> Some (meet_objs x y) in
       Object (tagged, untagged)

    | Base (l, s, td, args), Base (l', s', td', args'), pol when s = s' ->
       Base (Location.join l l', s, td, List.map2 (fun a a' -> match a, a' with
       | APos t, APos t' -> APos (f pol t t')
       | ANeg t, ANeg t' -> ANeg (f (polneg pol) t t')
       | ANegPos (s, t), ANegPos (s', t') -> ANegPos (f (polneg pol) s s', f pol t t')
       | ANone, ANone -> ANone
       | _, _ -> failwith "incompatible arguments to named type") args args')

    | _, _, _ ->
       assert (cmp_component x y); assert false

  let lte (type a) (type b) f (x : a t) (y : b t) = match x, y with
    | Func (pos, kwargs, reqs, (l, res)), Func (pos', kwargs', reqs', (l', res')) when cmp_component x y ->
       let kw_cmp r =
         SMap.fold (fun k (l', t') r ->
           if SMap.mem k kwargs then
             let (l, t) = SMap.find k kwargs in
             f Neg t t' @ r
           else [locations x, l', Unknown_kwarg k] @ r) kwargs' r in
       let req_cmp r =
         SMap.fold (fun k () r ->
           if SMap.mem k reqs' then r else
             [locations x, locations y, Missing_req_kwarg k] @ r) reqs r in
       f Pos res res' |> req_cmp |> kw_cmp |>
           List.fold_right2 (fun (l, x) (l, y) r -> f Neg x y @ r) pos pos'

    | Object (xtagged, xuntagged), Object (ytagged, yuntagged) -> 
       let lte_obj ox oy r =
         SMap.fold (fun k (yl, yk) r -> 
           if SMap.mem k ox then
             let (xl, xk) = SMap.find k ox in
             f Pos xk yk @ r
           else [locations x, yl, Missing_field k] @ r) oy r in
       []
       |> SMap.fold (fun tag ox r ->
         match SMap.find tag ytagged with
         | oy -> lte_obj ox oy r
         | exception Not_found ->
            match yuntagged with
            | Some oy -> lte_obj ox oy r
            | None -> [locations x, locations y, Missing_case (Some tag)] @ r) xtagged
       |> (fun r -> match xuntagged, yuntagged with
         | Some ox, Some oy -> lte_obj ox oy r
         | None, _ -> r
         | Some ox, None -> [locations x, locations y, Missing_case None] @ r)

    | Base (l, s, td, args), Base (l', s', td', args') when s = s' ->
       List.fold_right2 (fun arg arg' r -> (match arg, arg' with
       | APos t, APos t' -> f Pos t t'
       | ANeg t, ANeg t' -> f Neg t t'
       | ANegPos (s, t), ANegPos (s', t') -> f Neg s s' @ f Pos t t'
       | ANone, ANone -> []
       | _, _ -> failwith "internal error: incompatible arguments to named type") @ r) args args' []

    (* error cases *)
    | Func (pos, _, _, _), Func (pos', _, _, _) when List.length pos <> List.length pos' ->
       [locations x, locations y, Wrong_arity (List.length pos, List.length pos')]

    | x, y ->
       let name = function
       | Func _ -> `Func
       | Object _ -> `Obj
       | Base (_, s, td, args) -> `Base (match td with TAlias (name, _, _) | TOpaque (name, _) -> name) in
       [locations x, locations y, Incompatible_type (name x, name y)]

  let lte' f x y =
    let excuse = Wrong_arity (0, 1) in
    lte (fun p x y -> if f p x y then [] else [Location.empty, Location.empty, excuse]) x y = []

  let list_fields = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.mapi (fun i (l, a) -> (string_of_int i, a)) pos @
         (SMap.bindings kwargs |> List.map (fun (k, (l, a)) -> (Symbol.to_string k, a))) @
         ["res", res]
    | Object (tagged, untagged) -> 
       let list_obj p o r =
         List.map (fun (k, (_, v)) -> (p ^ Symbol.to_string k, v)) (SMap.bindings o) @ r in
       SMap.fold (fun tag o r ->
         list_obj (Symbol.to_string tag ^ "/") o r) tagged
         (match untagged with
         | None -> []
         | Some o -> list_obj "" o [])
    | Base (l, s, td, args) -> args |> List.mapi (fun i arg -> match arg with
      | APos t -> [string_of_int i ^ "+", t]
      | ANeg t -> [string_of_int i ^ "-", t]
      | ANegPos (s, t) -> [string_of_int i ^ "-", s; string_of_int i ^ "+", t]
      | ANone -> []) |> List.concat
end



type tyvar = Symbol.t

type typaram =
| TParam of Variance.variance option * Symbol.t
| TNoParam


type +'a tyargterm =
| VarSpec of 'a tyarg
| VarUnspec of 'a

type typeterm =
| TZero of Variance.polarity
| TNamed of tyvar * typeterm tyargterm list
| TCons of typeterm Components.t
| TAdd of Variance.polarity * typeterm * typeterm
| TRec of tyvar * typeterm
| TWildcard


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
  | (n, (TAlias (_, params, _) | TOpaque (_, params))) ->
     let params = params |> Array.to_list |> List.map (fun (v, n) -> v) in
     Some (n, params)
  | exception Not_found -> None

let name_of_stamp ctx stamp =
  match StampMap.find stamp ctx.by_stamp with
  | (n, _) -> n
  | exception Not_found -> failwith "unbound stamp"


let ty_fun pos kwargs res loc = Components.Func (
  List.map (fun a -> (Location.one loc, a loc)) pos,
  SMap.map (fun (a, req) -> (Location.one loc, a loc)) kwargs,
  SMap.filter (fun k (a, req) -> req) kwargs |> SMap.map (fun _ -> ()),
  (Location.one loc, res loc))
let ty_obj_cases tag def loc =
  let obj o = SMap.map (fun x -> (Location.one loc, x loc)) o in
  Components.Object (
    SMap.map obj tag,
    match def with Some o -> Some (obj o) | None -> None)
let ty_obj_tag t o loc =
  let obj = SMap.map (fun x -> (Location.one loc, x loc)) o in
  match t with
  | Some t -> Components.Object (SMap.singleton t obj, None)
  | None -> Components.Object (SMap.empty, Some obj)
let ty_obj o loc = ty_obj_tag None o loc
let ty_obj_l o loc =
  let o = List.fold_left (fun o (v, t) -> SMap.add v t o) SMap.empty o in
  ty_obj o loc

let ty_base ctx s args loc =
  match StampMap.find s ctx.by_stamp with
  | (name, td) -> Components.Base (Location.one loc, s, td, args)
  | exception Not_found -> failwith ("Unknown type with stamp " ^ string_of_int s)

let ty_named ctx name args loc =
  match find_by_name ctx name with
  | None -> failwith "unknown type"
  | Some (s, vars) -> begin
    if List.length args <> List.length vars then failwith "wrong arity to type ctor";
    let args = List.map2 (fun var arg -> match var, arg with
      | VPos, VarSpec (APos t) -> APos t
      | VNeg, VarSpec (ANeg t) -> ANeg t
      | VNegPos, VarSpec (ANegPos (s, t)) -> ANegPos (s, t)
      | VNegPos, VarSpec (APos t) -> ANegPos (TWildcard, t)
      | VNegPos, VarSpec (ANeg t) -> ANegPos (t, TWildcard)
      | VNone, VarSpec (ANone) -> ANone
      | _, VarSpec _ -> failwith "bad variance spec"

      | VPos, VarUnspec t -> APos t
      | VNeg, VarUnspec t -> ANeg t
      | VNegPos, VarUnspec t -> ANegPos (t, t)
      | VNone, VarUnspec t -> ANone
    ) vars args in
    ty_base ctx s args loc
  end

let ty_named' ctx name args loc =
  match find_by_name ctx name with
  | None -> failwith "unknown type"
  | Some (s, vars) -> begin
    assert (List.length args = List.length vars);
    ty_base ctx s args loc
  end

let add_type_alias err name param_list term ctx =
  let rec mk_params i s = function
    | [] -> s
    | TNoParam :: ps ->
       mk_params (i+1) s ps
    | TParam (v, p) :: ps ->
       mk_params (i+1) (if SMap.mem p s then failwith "duplicate param" else SMap.add p i s) ps in
  let param_idx = mk_params 0 SMap.empty param_list in
  let rec inferred_variances = ref (SMap.map (fun _ -> VNone) param_idx) in
  let use param pol =
    inferred_variances := 
      SMap.add param (vjoin 
        (SMap.find param !inferred_variances)
        (variance_of_pol pol)) !inferred_variances in

  let rec check pol = function
    | TNamed (t, []) when SMap.mem t param_idx ->
       (use t pol; BParam (SMap.find t param_idx))
    | TNamed (t, args) ->
       BCons (ty_named ctx t args Location.internal
                 |> Components.pmap check pol)
    | TCons cons -> BCons (Components.pmap check pol cons) 
    | TZero _ -> failwith "nzero"
    | TAdd _ -> failwith "nadd"
    | TRec _ -> failwith "nrec"  (* FIXME *)
    | TWildcard -> failwith "nwild" in

  let body = check Pos term in

  let param_variances = param_list
    |> List.map (function
      | TNoParam ->
         (VNone, None)
      | (TParam (v, p)) ->
         let v = match v, SMap.find p !inferred_variances with
           | None, infer -> infer
           | Some asc, infer -> 
              if not (vlte infer asc) then failwith ("incorrect variance annotation on " ^ Symbol.to_string p);
             asc in
         (v, Some p))
    |> Array.of_list in

  add_to_context err ctx name (TAlias (name, param_variances, body))

let add_opaque_type err name param_list ctx =
  let rec check_params acc seen = function
    | [] -> Array.of_list (List.rev acc)
    | TNoParam :: ps ->
       check_params ((VNone, None) :: acc) seen ps
    | TParam (v, p) :: ps ->
       if SMap.mem p seen then failwith "duplicate param" else
         match v with
         | None -> failwith "variance required"
         | Some v ->
            check_params ((v, Some p) :: acc) (SMap.add p () seen) ps in
  add_to_context err ctx name (TOpaque (name, check_params [] SMap.empty param_list))


let get_stamp = function
  | Components.Base (_, s, TAlias _, _) -> s
  | _ -> builtin_stamp

let rec expand args pol = function
| BParam p -> BParam
   (match pol, args.(p) with
   | Pos, APos t -> t
   | Pos, ANegPos (_, t) -> t
   | Neg, ANeg t -> t
   | Neg, ANegPos (t, _) -> t
   | _, _ ->  failwith "internal error: variance mismatch")
| BCons c -> BCons (pmap (expand args) pol c)

let expand_alias = function
  | Components.Base (_, s, TAlias (_, params, body), args) ->
     (match body with
     | BParam _ -> failwith "Non-contractive type alias"
     | BCons c ->
        pmap (expand (Array.of_list args)) Pos c)
  | _ -> failwith "Attempt to expand a type which is not an alias"
