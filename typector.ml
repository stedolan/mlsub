open Variance

type 'a printer = Format.formatter -> 'a -> unit

module SMap = Symbol.Map

type stamp = int


type +'a tyarg =
| APos of 'a
| ANeg of 'a
| ANegPos of 'a * 'a
| ANone

type conflict =
  Location.set * Location.set * Error.conflict_reason


module Components = struct
  type +'a t =
    | Func of (Location.set * 'a) list * (Location.set * 'a) SMap.t * unit SMap.t * (Location.set * 'a)
    | Object of (Location.set * 'a) SMap.t
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
    | Object o -> SMap.fold (fun _ (l, _) locs -> Location.join l locs) o Location.empty
    | Base (l, _, _, ts) -> l

  let change_locations l' = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l', a)) pos, 
             SMap.map (fun (l, a) -> (l', a)) kwargs,
             reqs,
             (l', res))
    | Object o -> Object (SMap.map (fun (l, a) -> (l', a)) o)
    | Base (l, s, td, args) -> Base (l', s, td, args)

  let pmap f pol = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l, f (polneg pol) a)) pos,
             SMap.map (fun (l, a) -> (l, f (polneg pol) a)) kwargs,
             reqs,
             (l, f pol res))
    | Object o -> Object (SMap.map (fun (l, x) -> (l, f pol x)) o)
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

    | Object o -> SMap.fold (fun k (l, t) x -> f pol t x) o x
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

    | Base (l, s, td, args), Base (l', s', td', args'), pol when s = s' ->
       Base (Location.join l l', s, td, List.map2 (fun a a' -> match a, a' with
       | APos t, APos t' -> APos (f pol t t')
       | ANeg t, ANeg t' -> ANeg (f (polneg pol) t t')
       | ANegPos (s, t), ANegPos (s', t') -> ANegPos (f (polneg pol) s s', f pol t t')
       | ANone, ANone -> ANone
       | _, _ -> failwith "incompatible arguments to named type") args args')

    | _, _, _ ->
       assert (cmp_component x y); assert false

  let lte (type a) (type b) f (x : a t) (y : b t) = let open Error in match x, y with
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

    | Object ox, Object oy -> 
       SMap.fold (fun k (yl, yk) r -> 
         if SMap.mem k ox then
           let (xl, xk) = SMap.find k ox in
           f Pos xk yk @ r
         else [locations x, yl, Missing_field k] @ r) oy []

    | Base (l, s, td, args), Base (l', s', td', args') when s = s' ->
       List.fold_right2 (fun arg arg' r -> (match arg, arg' with
       | APos t, APos t' -> f Pos t t'
       | ANeg t, ANeg t' -> f Neg t t'
       | ANegPos (s, t), ANegPos (s', t') -> f Neg s s' @ f Pos t t'
       | ANone, ANone -> []
       | _, _ -> Error.internal "incompatible arguments to named type") @ r) args args' []

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
    let excuse = Error.Wrong_arity (0, 1) in
    lte (fun p x y -> if f p x y then [] else [Location.empty, Location.empty, excuse]) x y = []

  let list_fields = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.mapi (fun i (l, a) -> (string_of_int i, a)) pos @
         (SMap.bindings kwargs |> List.map (fun (k, (l, a)) -> (Symbol.to_string k, a))) @
         ["res", res]
    | Object o -> List.map (fun (k, (_, v)) -> (Symbol.to_string k, v)) (SMap.bindings o)
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



let comma ppf () = Format.fprintf ppf ",@ "

let printp paren pr ppf = let open Format in
  let openbox ppf = if paren then fprintf ppf "@[(" else fprintf ppf "@[" in
  let closebox ppf = if paren then fprintf ppf "@])" else fprintf ppf "@]" in
  openbox ppf;
  kfprintf closebox ppf "%a" pr


let print_comp pb ctx pr ppf = let open Components in function
  | Func (pos, kwargs, reqs, (l, res)) ->
     let args = List.map (fun (l, a) -> (None, Some a)) pos @
       (SMap.merge (fun k arg req -> match arg, req with
        | Some (l, a), None -> Some (Some (Symbol.to_string k ^ "?"), Some a)
        | Some (l, a), Some () -> Some (Some (Symbol.to_string k), Some a)
        | None, Some () -> Some (Some (Symbol.to_string k), None)
        | None, None -> None) kwargs reqs |> SMap.bindings |> List.map (fun (a, b) -> b)) in
     let pr_arg ppf = function
       | None, None -> ()
       | None, Some t -> Format.fprintf ppf "%a" (pr false) t
       | Some name, Some t -> Format.fprintf ppf "%s : %a" name (pr false) t
       | Some name, None -> Format.fprintf ppf "%s : <err>" name in
     let comma ppf () = Format.fprintf ppf ",@ " in
     let need_paren = match args with [None, Some _] -> false | _ -> true in
     Format.fprintf ppf (if pb then "%a -> %a" else "(%a -> %a)")
       (printp need_paren (Format.pp_print_list ~pp_sep:comma pr_arg)) args
       (pr false) res
  | Object _ as o ->
     let rec pfield ppf = function
       | [] -> ()
       | [f, x] ->
          Format.fprintf ppf "%s :@ %a" f (pr false) x
       | (f, x) :: xs ->
          Format.fprintf ppf "%s :@ %a,@ %a" f (pr false) x pfield xs in
     Format.fprintf ppf "{%a}" pfield (list_fields o)
  | Base (l, s, td, []) ->
     Format.fprintf ppf "%s" (Symbol.to_string (name_of_stamp ctx s))
  | Base (l, s, (TAlias (_, params, _) | TOpaque (_, params)), args) ->
     let pb = match args with [_] -> true | _ -> false in
     let print_arg ppf = function
       | VPos, APos t -> Format.fprintf ppf "%a" (pr pb) t
       | _, APos t -> Format.fprintf ppf "+%a" (pr pb) t 
       | VNeg, ANeg t -> Format.fprintf ppf "%a" (pr pb) t
       | _, ANeg t -> Format.fprintf ppf "-%a" (pr pb) t
       | _, ANegPos (s, t) -> Format.fprintf ppf "-%a +%a" (pr false) s (pr false) t
       | _, ANone -> Format.fprintf ppf "_" in
     Format.fprintf ppf "%s[%a]" (Symbol.to_string (name_of_stamp ctx s)) 
       (Format.pp_print_list ~pp_sep:comma print_arg) 
       (List.map2 (fun (v, _) b -> v , b) (Array.to_list params) args)


let needs_paren p = function
  | TRec _ -> true
  | TAdd (p', t1, t2) -> not (p = p')
  | TCons (Func _) -> true
  | _ -> false

(* pb is true: delimited by context
   pb is false: this should this be self-delimiting. *)
let rec print_typeterm ctx pb ppf = let open Format in function
  | TZero Pos -> fprintf ppf "nothing"
  | TZero Neg -> fprintf ppf "any"
  | TNamed (v, []) ->
     fprintf ppf "%s" (Symbol.to_string v)
  | TNamed (v, args) -> 
     let pb' = match args with [_] -> true | _ -> false in
     let print_arg ppf = function
       | VarSpec (APos t) -> fprintf ppf "+%a" (print_typeterm ctx pb') t
       | VarSpec (ANeg t) -> fprintf ppf "-%a" (print_typeterm ctx pb') t
       | VarSpec (ANegPos (s, t)) -> fprintf ppf "-%a +%a"
          (print_typeterm ctx false) s (print_typeterm ctx false) t
       | VarSpec (ANone) -> fprintf ppf "_"
       | VarUnspec t -> fprintf ppf "%a" (print_typeterm ctx pb') t in
     fprintf ppf "%s[%a]" (Symbol.to_string v) (Format.pp_print_list ~pp_sep:comma print_arg) args
  | TCons cons ->
     fprintf ppf "@[%a@]" (print_comp pb ctx (print_typeterm ctx)) cons
  | TAdd (p, _, _) as t ->
     if pb then
       fprintf ppf "@[%a@]" (print_sum p ctx) t
     else
       fprintf ppf "@[(%a)@]" (print_sum p ctx) t
  | TRec (v, t) ->
    (* FIXME paren placement ok? *)
    fprintf ppf "rec %s = %a" (Symbol.to_string v) (print_typeterm ctx false) t
  | TWildcard ->
    fprintf ppf "_"
and print_sum p ctx ppf = let open Format in function
| TAdd (p', t1, t2) when p' = p ->
   fprintf ppf "%a %s@ %a"
     (print_sum p ctx) t1
     (match p with Pos -> "|" | Neg -> "&")
     (print_sum p ctx) t2
| t -> print_typeterm ctx false ppf t


let print_typeterm ctx = print_typeterm ctx true

let ty_fun pos kwargs res loc = Components.Func (
  List.map (fun a -> (Location.one loc, a loc)) pos,
  SMap.map (fun (a, req) -> (Location.one loc, a loc)) kwargs,
  SMap.filter (fun k (a, req) -> req) kwargs |> SMap.map (fun _ -> ()),
  (Location.one loc, res loc))
let ty_obj o loc = Components.Object (SMap.map (fun x -> (Location.one loc, x loc)) o)
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
