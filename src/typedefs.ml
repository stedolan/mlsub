(*
 * Core definitions used by the typechecker
 *)
open Util

module StrMap = Map.Make (struct type t = string let compare = compare end)


let equal_lists f p q =
  try List.for_all2 f p q
  with Invalid_argument _ -> false

let rec compare_lists f p q =
  match p, q with
  | [], [] -> 0
  | p::ps, q::qs ->
     let cmp = f p q in
     if cmp = 0 then compare_lists f ps qs else cmp
  | [], _::_ -> -1
  | _::_, [] -> 1


module Cons = struct
  open Tuple_fields

  (* Head type constructors. These do not bind type variables. *)
  type (+'neg, +'pos) t =
    (* FIXME: maybe delete these once abstypes exist? *)
    | Bool
    | Int
    | String
    | Record of 'pos tuple_fields
    | Func of 'neg tuple_fields * 'pos


  let equal_one ~neg ~pos p q =
    match p, q with
    | Bool, Bool -> true
    | Int, Int -> true
    | String, String -> true
    | Record p, Record q ->
       equal_fields pos p q
    | Func (pa, pr), Func (qa, qr) ->
       equal_fields neg pa qa && pos pr qr
    | (Bool|Int|String|Record _|Func _), _ -> false

  (* same_component isn't quite right: the lattice is more complicated
     than that because of Record(Closed) *)
  let same_component p q =
    match p, q with
    | Bool, Bool
    | Int, Int
    | String, String
    | Record _, Record _
    | Func _, Func _
      -> true
    | (Bool|Int|String|Record _|Func _), _ -> false

  let map_one ~neg ~pos = function
    | Bool -> Bool
    | Int -> Int

    | String -> String
    | Record fields -> Record (map_fields (fun _fn x -> pos x) fields)
    | Func (args, res) ->
       let args = map_fields (fun _fn x -> neg x) args in
       let res = pos res in
       Func (args, res)

  type field_neg =
    | Func_arg of Tuple_fields.field_name

  type field_pos =
    | Record_field of Tuple_fields.field_name
    | Func_res

  type field = F_neg of field_neg | F_pos of field_pos

  let equal_field_neg a b =
    match a, b with
    | Func_arg a, Func_arg b -> Tuple_fields.equal_field_name a b

  let equal_field_pos a b =
    match a, b with
    | Record_field a, Record_field b -> Tuple_fields.equal_field_name a b
    | Func_res, Func_res -> true
    | _ -> false

  let equal_field a b =
    match a, b with
    | F_neg a, F_neg b -> equal_field_neg a b
    | F_pos a, F_pos b -> equal_field_pos a b
    | _ -> false

  let mapi_one ~neg ~pos = function
    | Bool -> Bool
    | Int -> Int

    | String -> String
    | Record fields -> Record (map_fields (fun fn x -> pos (Record_field fn) x) fields)
    | Func (args, res) ->
       let args = map_fields (fun fn x -> neg (Func_arg fn) x) args in
       let res = pos Func_res res in
       Func (args, res)


  module One_or_two = struct
    type ('a, 'b) t =
      | L of 'a
      | R of 'b
      | LR of 'a * 'b

    let left x = L x
    let right x = R x
    let both x y = LR (x,y)
  end

  (* meet and join return None iff not same_component *)

  let meet_one a b =
    match a, b with
    | Bool, Bool -> Some Bool
    | Int, Int -> Some Int
    | String, String -> Some String
    | (Bool|Int|String), _ | _, (Bool|Int|String) -> None

    | Record c, Record c' ->
       Option.map (fun r -> Record r)
         One_or_two.(Tuple_fields.union ~left ~right ~both c c')

    | Func (args, res), Func (args', res') ->
       (* FIXME: fail here rather than assuming variadic functions?
          Could/should enforce that functions are always `Closed *)
       let args = One_or_two.(Tuple_fields.inter ~both) args args' in
       Some (Func (args, LR (res, res')))

    | Record _, Func _ | Func _, Record _ -> None

  let join_one a b =
    assert (same_component a b); (* FIXME *)
    match a, b with
    | Bool, Bool -> Bool
    | Int, Int -> Int
    | String, String -> String
    | (Bool|Int|String), _ | _, (Bool|Int|String) -> assert false
  
    | Record c, Record c' ->
       Record One_or_two.(Tuple_fields.inter ~both c c')
  
    | Func (args, res), Func (args', res') ->
       (* FIXME: components wrong here? Check variadic functions, are these possible? *)
       begin match One_or_two.(Tuple_fields.union ~left ~right ~both args args') with
       | Some r ->
          let res =
            if true then One_or_two.both res res'
            else (if false then One_or_two.left res else One_or_two.right res')
          in
          Func (r, res)
       | None -> assert false
       end
  
    | Record _, Func _ | Func _, Record _ -> assert false

  type cons_head = (unit, unit) t list

  (* FIXME: can intern these if it turns out to be slow *)
  type cons_loc = cons_head * Location.t
  module Locs = UniqList.Make (struct
    type nonrec t = cons_loc
    let equal (a, _) (b, _) = equal_lists (equal_one ~neg:(fun () () -> true) ~pos:(fun () () -> true)) a b
  end)


  type ('n,'p) conses = {
    (* At most one of each component *)
    (* FIXME: enforce *)
    conses: ('n, 'p) t list;
    locs: Locs.t
   }

  let equal ~neg ~pos a b = equal_lists (equal_one ~neg ~pos) a.conses b.conses

  let map ~neg ~pos t = { conses = List.map (map_one ~neg ~pos) t.conses; locs = t.locs }
  let mapi ~neg ~pos t = { conses = List.map (mapi_one ~neg ~pos) t.conses; locs = t.locs }

  let rec join a b =
    match a with
    | [] -> List.map (map_one ~neg:One_or_two.right ~pos:One_or_two.right) b
    | ac :: arest ->
       let bc, brest = List.partition (same_component ac) b in
       match bc with
       | [] ->
          map_one ~neg:One_or_two.left ~pos:One_or_two.left ac ::
            join arest brest
       | [bc] ->
          join_one ac bc ::
            join arest brest
       | _ :: _ :: _ ->
          failwith "multiple joinable conses"

  let join a b = { conses = join a.conses b.conses; locs = Locs.append a.locs b.locs ~merge:(fun a _ -> a) }

  let meet a b =
    a |> List.concat_map (fun a ->
      b |> List.concat_map (fun b ->
        match meet_one a b with
        | None -> []
        | Some m -> [m]))

  let meet a b = { conses = meet a.conses b.conses; locs = Locs.append a.locs b.locs ~merge:(fun a _ -> a) }

  let bottom = { conses = []; locs = Locs.empty }
  let bottom_loc loc = { conses = []; locs = Locs.single ([], loc) }
  let is_bottom = function { conses = []; _ } -> true | _ -> false

  let get_single = function { conses = [c]; _ } -> Some c | _ -> None

  let make ~loc c = { conses = [c]; locs = Locs.single ([map_one ~pos:ignore ~neg:ignore c], loc) }

  type ('neg, 'pos) subfield =
    | S_neg of field_neg * 'neg
    | S_pos of field_pos * 'pos

  type field_conflict = [`Missing of field_name | `Extra of field_name option]
  type conflict =
    | Fields of field_conflict
    | Args of field_conflict
    | Incompatible


  type subtype_error =
    {
      conflict: conflict;
      (* more specific mismatch *)
      located: ((cons_head * Location.t) * (cons_head * Location.t)) option;
    }

  exception FieldError of field_conflict
  let subtype_fields ~sub af bf =
    if bf.fopen = `Closed then begin
      if af.fopen = `Open then raise (FieldError (`Extra None));
      (* check dom a ⊆ dom b *)
      List.iter (fun k ->
        match FieldMap.find k bf.fields with
        | exception Not_found -> raise (FieldError (`Extra (Some k)))
        | _ -> ()) af.fnames
    end;
    FieldMap.bindings bf.fields |> List.map (fun (k, b) ->
      match FieldMap.find k af.fields with
      | exception Not_found -> raise (FieldError (`Missing k))
      | a -> sub k (a, b))

  let subtype_one a b =
    match a, b with
    | Bool, Bool
    | Int, Int
    | String, String -> Ok []
    | Func (args, res), Func (args', res') ->
       begin match subtype_fields ~sub:(fun k s -> S_neg (Func_arg k, s)) args' args with
       | sub -> Ok (sub @ [S_pos (Func_res, (res, res'))])
       | exception FieldError con -> Error (Args con)
       end
    | Record fs, Record fs' ->
       begin match subtype_fields ~sub:(fun k s -> S_pos (Record_field k, s)) fs fs' with
       | sub -> Ok sub
       | exception FieldError con -> Error (Fields con)
       end
    | _, _ -> Error Incompatible

  let partition_results x =
    List.partition_map (function Ok x -> Left x | Error x -> Right x) x

  let subtype' a b =
    let parts =
      a |> List.map (fun a ->
        (* At most one of these should hold *)
        match partition_results (List.map (fun b -> subtype_one a b) b) with
        | [s], _ -> Ok s
        | [], [] -> Error (a, Incompatible)
        | [], e :: _ -> Error (a, e)
        (* FIXME: prove this does not occur *)
        | _ :: _ :: _, _ -> intfail "bad cons join - unmerged ctors")
    in
    match partition_results parts with
    | subs, [] -> Ok (List.concat subs)
    | _, err :: _ -> Error err

  let subtype a b =
    match subtype' a.conses b.conses with
    | Ok subs -> Ok subs
    | Error (lhs, conflict) ->
       let located =
         (a.locs :> cons_loc list) |> List.find_map (fun (a, al) ->
           if Result.is_error (subtype' a [lhs]) then None
           else (b.locs :> cons_loc list) |> List.find_map (fun (b, bl) ->
             if Result.is_ok (subtype' a b) then None
             else Some ((a, al), (b, bl))))
       in
       Error { conflict;
               located }
end

module SymMap = Tuple_fields.SymMap

module Env_level : sig
  type t

  val initial : t
  val extend : t -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val extends : t -> t -> bool

  val min : t -> t -> t
  val max : t -> t -> t

  val to_int : t -> int
end = struct
  (* Not actually mutable, but marking it as such
     makes physical equality work *)
  type t =
    { mutable level : int }

  let initial = { level = 0 }
  let extend { level } = { level = level + 1 }

  let compare { level=l1} {level=l2} = compare l1 l2

  let extends {level=l1} {level=l2} = l1 <= l2

  let equal l1 l2 =
    if l1.level = l2.level then
      (assert (l1 == l2); true)
    else
      false

  let min l1 l2 = if extends l1 l2 then l1 else l2
  let max l1 l2 = if extends l2 l1 then l1 else l2

  let to_int l = l.level
end

type env_level = Env_level.t

(* Rigid variables are immutable.
   Their bounds are stored in the environment. *)
type rigvar =
  { level: env_level;
    var: int }

let equal_rigvar (p : rigvar) (q : rigvar) =
  Env_level.equal p.level q.level && p.var = q.var

let compare_rigvar (p : rigvar) (q : rigvar) =
  (* negate: sort highest level earliest *)
  let cmp = ~- (compare (Env_level.to_int p.level) (Env_level.to_int q.level)) in
  if cmp <> 0 then cmp else
    (assert (Env_level.equal p.level q.level); compare p.var q.var)

(* Sets of rigid variables *)
module Rvset = UniqList.Make (struct
  type t = rigvar * Location.t
  let equal (rv, _) (rv', _) = equal_rigvar rv rv'
end)

(* A ctor_ty is a join of a constructed type and some rigid variables *)
type (+'neg,+'pos) ctor_ty =
  { cons: ('neg,'pos) Cons.conses;
    rigvars: Rvset.t }

(* Flexvars are mutable but only in one direction.
     - level may decrease
     - bounds may become tighter (upper decreases, lower increases) *)
type flexvar =
  { level: env_level;
    mutable upper: styp_neg list; (* strictly covariant parts are matchable *)
    mutable lower: flex_lower_bound;
    id: int;    (* for printing/sorting *)
    mutable gen: flexvar_gen;
    mutable rotated: bool
  }

(* A well-formed negative styp is either:
     - a single flexible variable
     - a constructed type, possibly joined with some rigid variables *)
and styp_neg =
  | UBvar of flexvar
    (* Only one allowed per set of rigid variables *)
  | UBcons of (flex_lower_bound, flexvar) ctor_ty

(* Matchability constraint: the contravariant parts of a flexible variable's lower bound must be flexible variables.
   Flexible variables appearing in vars must not have UBvar upper bounds, as they are also constrained above here.
   Flexible variables appearing negatively in ctor might well have UBvar upper bounds.
 *)
and flex_lower_bound =
  | Lower of flexvar UniqList.t * (flexvar, flex_lower_bound) ctor_ty
  | Ltop of Location.t option

(* Variables in typs *)
and typ_var =
  | Vbound of {index: int; var:int}
  | Vrigid of rigvar

(* Temporary structure used during generalisation *)
and flexvar_gen_visit_counts = { mutable pos : int; mutable neg : int }

and flexvar_gen_status =
  | No_var_chosen
  | Computing_bound
  | Generalised of int
  | Kept of flexvar
  | Replace_with_rigid of rigvar * Location.t

and flexvar_gen =
  | Not_generalising
  | Generalising of {
      level: env_level;
      visit : flexvar_gen_visit_counts;
      mutable bound_var : flexvar_gen_status
    }


module Fvset = UniqList.Make(struct type t = flexvar let equal = (==) end)

(* FIXME: enforce tjoin invariants, especially in neg types *)
type (+'neg, +'pos) typ =
  | Tsimple of 'pos
  | Ttop of Location.t option
  (* Bottom is represented as an empty Tcons *)
  | Tcons of ('neg, 'pos) cons_typ
  | Tvar of Location.t option * typ_var
  | Tjoin of ('neg, 'pos) typ * ('neg, 'pos) typ
     (* No Tpoly allowed under a Tjoin *)
  | Tpoly of ('neg, 'pos) poly_typ
and (+'neg, +'pos) cons_typ = (('pos, 'neg) typ, ('neg, 'pos) typ) Cons.conses
and (+'neg, +'pos) poly_typ =
  { (* names must be distinct *)
    (* bound must be a constructed type, possibly joined with some rigid/bound vars *)
    vars : (string Location.loc * ('pos, 'neg) typ option) iarray;
    body : ('neg, 'pos) typ }

type ptyp = (flexvar, flex_lower_bound) typ
type ntyp = (flex_lower_bound, flexvar) typ

type value_binding =
  { typ: ptyp;
    (* The level of the outermost unannotated lambda-bound parameter
       reachable from this binding by expanding untyped let definitions.
       (cf. Haskell's MonoLocalBinds) *)
    gen_level: env_level option; }

type env =
  | Env_vals of { vals : value_binding SymMap.t; rest : env }
  | Env_types of {
     level : env_level;
     rig_names : int SymMap.t;
     rig_defns : rigvar_defn iarray;
     rest : env }
  | Env_nil

(* Rigid type variables. *)
and rigvar_defn = {
  (* unique among a binding group, but can shadow.
     Only used for parsing/printing: internally, referred to by index. *)
  name : string Location.loc;
  upper : (flexvar, flex_lower_bound) Cons.conses option;
}

(*
 * Equality checks (Syntactic, not subtyping-aware, ignore locations)
 *)

let equal_flexvar (p : flexvar) (q : flexvar) =
  p == q
let rec equal_flex_lower_bound (p : flex_lower_bound) (q : flex_lower_bound) =
  match p, q with
  | Ltop _, Ltop _ -> true
  | Lower (pflex, pctor), Lower (qflex, qctor) ->
     Fvset.equal pflex qflex &&
     Rvset.equal pctor.rigvars qctor.rigvars &&
     Cons.equal ~neg:equal_flexvar ~pos:equal_flex_lower_bound pctor.cons qctor.cons
  | _, _ -> false
let equal_styp_neg (p : styp_neg) (q : styp_neg) =
  match p, q with
  | UBvar pv, UBvar qv -> equal_flexvar pv qv
  | UBcons cp, UBcons cq ->
     Rvset.equal cp.rigvars cq.rigvars &&
     Cons.equal ~neg:equal_flex_lower_bound ~pos:equal_flexvar cp.cons cq.cons
  | (UBvar _|UBcons _), _ -> false

let bottom = Lower(Fvset.empty, {cons=Cons.bottom;rigvars=Rvset.empty})
let of_flexvars fvs = Lower(fvs, {cons=Cons.bottom;rigvars=Rvset.empty})
let of_flexvar fv = of_flexvars (Fvset.single fv)
let of_rigvars rigvars = Lower(Fvset.empty, {cons=Cons.bottom;rigvars})
let of_rigvar loc rv = of_rigvars (Rvset.single (rv, loc))
let is_bottom t = equal_flex_lower_bound bottom t

(*
 * Flexvar mutations and backtracking log
 *)

type flexvar_change =
  | Change_expanded_mark (* hack for logging expand changes *)
  (* | Change_level of flexvar * env_level *)
  | Change_upper of flexvar * styp_neg list
  | Change_lower of flexvar * flex_lower_bound

(*
let fv_set_level ~changes fv level =
  assert (Env_level.extends level fv.level);
  if not (Env_level.equal level fv.level) then begin
    changes := Change_level (fv, fv.level) :: !changes;
    fv.level <- level;
    (* Cancel any generalisation in progress (see expand) *)
    if fv.gen <> Not_generalising then fv.gen <- Not_generalising;
  end
*)

let fv_set_upper ~changes fv upper =
  changes := Change_upper (fv, fv.upper) :: !changes;
  fv.upper <- upper

let fv_set_lower ~changes fv lower =
  begin match lower with Lower (fvs, _) -> assert (not (Fvset.mem fv fvs)) | Ltop _ -> () end;
  changes := Change_lower (fv, fv.lower) :: !changes;
  fv.lower <- lower

let fv_maybe_set_lower ~changes fv lower =
  if not (equal_flex_lower_bound fv.lower lower) then
    (fv_set_lower ~changes fv lower; true)
  else false

let fv_maybe_set_upper ~changes (fv : flexvar) upper =
  if not (equal_lists equal_styp_neg fv.upper upper) then
    (fv_set_upper ~changes fv upper; true)
  else false

let revert changes =
  changes |> List.iter (function
  | Change_expanded_mark -> ()
  (* | Change_level (fv, level) -> fv.level <- level *)
  | Change_upper (fv, upper) -> fv.upper <- upper
  | Change_lower (fv, lower) -> fv.lower <- lower)

let commit ~changes rest =
  changes := rest @ !changes

(*
 * Environment ordering
 *)

let rec env_at_level env lvl =
  match env with
  | Env_vals { vals=_; rest } -> env_at_level rest lvl
  | Env_types tys when Env_level.equal tys.level lvl -> env
  | Env_types tys ->
     assert (Env_level.extends lvl tys.level); env_at_level tys.rest lvl
  | Env_nil when Env_level.equal Env_level.initial lvl -> Env_nil
  | Env_nil -> intfail "env level not found"

let env_rigid_vars env lvl =
  match env_at_level env lvl with
  | Env_types tys ->
     assert (Env_level.equal tys.level lvl); tys.rig_defns
  | _ -> intfail "env_rigid_vars"

let env_rigid_var env (rv : rigvar) =
  IArray.get (env_rigid_vars env rv.level) rv.var

let env_rigid_bound env (rv : rigvar) =
  let r = env_rigid_var env rv in
  r.upper

let rec env_level env =
  match env with
  | Env_types tys -> tys.level
  | Env_vals vs -> env_level vs.rest
  | Env_nil -> Env_level.initial

(* visit counters: odd = visiting, even = done *)
let fv_gen_visit_counts env fv =
  let level = env_level env in
  assert (Env_level.extends fv.level level);
  if not (Env_level.equal fv.level level) then None
  else match fv.gen with
  | Generalising g ->
     assert (Env_level.equal fv.level g.level);
     Some g.visit
  | Not_generalising ->
     let visit = { pos = 0; neg = 0 } in
     fv.gen <- Generalising { level = fv.level; visit; bound_var = No_var_chosen };
     Some visit

type visit_type = First_visit | Recursive_visit
let fv_gen_visit_pos env visit fv k =
  match fv_gen_visit_counts env fv with
  | None -> ()
  | Some v ->
     assert (v.pos <= visit);
     if v.pos = visit then () (* visited already *)
     else if v.pos = visit - 1 then k Recursive_visit
     else begin
       v.pos <- visit - 1;
       k First_visit;
       v.pos <- visit
     end
let fv_gen_visit_neg env visit fv k =
  match fv_gen_visit_counts env fv with
  | None -> ()
  | Some v ->
     assert (v.neg <= visit);
     if v.neg = visit then () (* visited already *)
     else if v.neg = visit - 1 then k Recursive_visit
     else begin
       v.neg <- visit - 1;
       k First_visit;
       v.neg <- visit
     end


(*
 * Opening/closing of binders
 *)

(* Assert that a typ contains no Vbound *)
let assert_locally_closed_var ix = function
  | Vrigid _ -> ()
  | Vbound {index; _} -> assert (index < ix)

let rec assert_locally_closed :
  'a 'b . int -> ('a, 'b) typ -> unit =
  fun ix ty -> match ty with
  | Tsimple _ | Ttop _ -> ()
  | Tcons c -> ignore (Cons.map ~neg:(assert_locally_closed ix) ~pos:(assert_locally_closed ix) c)
  | Tvar (_, v) -> assert_locally_closed_var ix v
  | Tjoin (a, b) -> assert_locally_closed ix a; assert_locally_closed ix b
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     vars |> IArray.iter (fun (_, b) -> Option.iter (assert_locally_closed ix) b);
     assert_locally_closed ix body

let open_typ_var f loc ix = function
  | Vbound {index; var} when index >= ix ->
     assert (index = ix);
     let res = f loc var in
     assert_locally_closed ix res;
     res
  | v -> Tvar (loc, v)

let rec open_typ :
  'neg 'pos . 
    neg:(Location.t option -> int -> ('pos, 'neg) typ) ->
    pos:(Location.t option -> int -> ('neg, 'pos) typ) ->
    int -> ('neg, 'pos) typ -> ('neg, 'pos) typ =
  fun ~neg ~pos ix t -> match t with
  | (Tsimple _ | Ttop _) as s -> s
  | Tcons c -> Tcons (Cons.map ~neg:(open_typ ~neg:pos ~pos:neg ix) ~pos:(open_typ ~neg ~pos ix) c)
  | Tvar (l,v) -> open_typ_var pos l ix v
  | Tjoin (a,b) -> Tjoin (open_typ ~neg ~pos ix a, open_typ ~neg ~pos ix b)
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, Option.map (open_typ ~neg:pos ~pos:neg ix) b) vars;
            body = open_typ ~neg ~pos ix body}

let open_typ_rigid vars t =
  let mkv loc i = Tvar (loc, (Vrigid (IArray.get vars i))) in
  open_typ ~neg:mkv ~pos:mkv 0 t

let close_typ_var lvl f ~ispos ~isjoin index = function
  | Vrigid {level; _} as v when Env_level.equal lvl level ->
     Vbound {index; var = f v ~ispos ~isjoin}
  | v -> v

(* Can only be used on typs without Tsimple nodes.
   (This limits it to use during parsing, which does not generate Tsimple) *)
let rec close_typ :
  'a 'b . env_level -> (typ_var -> ispos:bool -> isjoin:bool -> int) -> simple:('a -> 'b)  -> ispos:bool -> isjoin:bool -> int -> ('a, 'a) typ -> ('b, 'b) typ
  = fun lvl var ~simple ~ispos ~isjoin ix ty -> match ty with
  | Tsimple z -> Tsimple (simple z)
  | Ttop _ as z -> z
  | Tcons c -> Tcons (Cons.map ~neg:(close_typ lvl var ~simple ~ispos:(not ispos) ~isjoin:false ix) ~pos:(close_typ lvl var ~simple ~ispos ~isjoin:false ix) c)
  | Tvar (l, v) -> Tvar (l, close_typ_var lvl var ~ispos ~isjoin ix v)
  | Tjoin (a, b) -> Tjoin(close_typ lvl var ~simple ~ispos ~isjoin:true ix a,
                          close_typ lvl var ~simple ~ispos ~isjoin:true ix b)
  | Tpoly {vars; body} ->
     assert (not isjoin);
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, Option.map (close_typ lvl var ~simple ~ispos:(not ispos) ~isjoin:false ix) b) vars;
            body = close_typ lvl var ~simple ~ispos ~isjoin:false ix body}

let diag x = (x, x)
let xs = diag []
let ys = (fst xs, snd xs)

let gen_zero : (zero, zero) typ -> ('a, 'b) typ = Obj.magic

let close_typ_rigid ~ispos level ty =
  let close_var v ~ispos ~isjoin =
    if isjoin && not ispos then failwith "contravariant join";
    match v with
    | Vrigid v when Env_level.equal v.level level -> v.var
    | _ -> intfail "close_typ_rigid: not a rigid variable" in
  close_typ level close_var ~simple:never ~ispos ~isjoin:false 0 ty |> gen_zero


let next_flexvar_id = ref 0
let fresh_flexvar level : flexvar =
  let id = !next_flexvar_id in
  incr next_flexvar_id;
  { level; upper = []; lower = bottom; id; gen = Not_generalising; rotated = false }


let rec env_lookup_type_var env name : rigvar option =
  match env with
  | Env_vals vs -> env_lookup_type_var vs.rest name
  | Env_types ts ->
     begin match SymMap.find name ts.rig_names with
     | var -> Some {level = ts.level; var}
     | exception Not_found -> env_lookup_type_var ts.rest name
     end
  | Env_nil -> None

let lookup_named_type loc = let open Cons in function
  | "any" -> Some (Ttop (Some loc))
  | "nothing" -> Some (Tcons (Cons.bottom_loc loc))
  | "bool" -> Some (Tcons (Cons.make ~loc Bool))
  | "int" -> Some (Tcons (Cons.make ~loc Int))
  | "string" -> Some (Tcons (Cons.make ~loc String))
  | _ -> None

let flexvar_name fv =
  let names = [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "κ"; "ν"; "ξ"; "π"; "ρ" |] in
  let id = fv.id in
  if id < Array.length names then names.(id)
  else Printf.sprintf "_%d" id


(*
 * Well-formedness checks.
 *)

let rec wf_flexvar ~seen env lvl (fv : flexvar) =
  if Hashtbl.mem seen fv.id then () else begin
  Hashtbl.add seen fv.id ();
  if not (Env_level.extends fv.level (env_level env)) then
    intfail "wf_flexvar: %s at %d not inside env %d" (flexvar_name fv) (Env_level.to_int fv.level) (Env_level.to_int (env_level env));
  assert (Env_level.extends fv.level (env_level env));
  assert (Env_level.extends fv.level lvl);
  if not (Env_level.equal fv.level Env_level.initial) then
    ignore (env_rigid_vars env fv.level);
  (* FIXME rectypes *)
  begin match fv.lower with Lower (fvs, _) -> assert (not (Fvset.mem fv fvs)) | Ltop _ -> () end;
  wf_flex_lower_bound ~seen env fv.level fv.lower;
  (* Rigvar sets must be distinct *)
  let rvsets = List.filter_map (function UBvar _ -> None | UBcons c -> Some c.rigvars) fv.upper in
  assert (List.length rvsets =
         List.length (rvsets |> List.concat_map (fun rv1 -> rvsets |> List.filter (Rvset.equal rv1))));
  fv.upper |> List.iter (function
  | UBvar v ->
     if fv.rotated then assert (not (Env_level.equal fv.level v.level));
     wf_flexvar ~seen env fv.level v
  | UBcons {cons;rigvars} ->
     (* Each rigvar set must contain all of the rigvars in the lower bound *)
     let rvlow =
       match fv.lower with
       | Lower (_, ctor) -> Rvset.to_list ctor.rigvars
       | Ltop _ -> []
     in
     (* Well-formedness of bounds *)
     rvlow |> List.iter (fun rv -> assert (Rvset.mem rv rigvars));
     Cons.map ~neg:(wf_flex_lower_bound ~seen env fv.level) ~pos:(wf_flexvar ~seen env fv.level) cons |> ignore)
  end

and wf_rigvar env lvl (rv : rigvar) =
  assert (Env_level.extends rv.level lvl);
  let rvs = env_rigid_vars env rv.level in
  assert (0 <= rv.var && rv.var < IArray.length rvs)

and wf_flex_lower_bound ~seen env lvl l =
  match l with
  | Ltop _ -> ()
  | Lower (flexvars, {cons;rigvars}) ->
     Fvset.iter ~f:(wf_flexvar ~seen env lvl) flexvars;
     List.iter (wf_rigvar env lvl) (List.map fst (Rvset.to_list rigvars));
     (* FIXME check distinctness of conses joined *)
     Cons.map ~neg:(wf_flexvar ~seen env lvl) ~pos:(wf_flex_lower_bound ~seen env lvl) cons |> ignore



let wf_var env ext = function
  | Vrigid rv -> wf_rigvar env rv.level rv
  | Vbound {index; var} ->
     assert (0 <= index && index < List.length ext);
     assert (0 <= var && var < snd (List.nth ext index))

let rec wf_typ : 'pos 'neg .
  neg:('neg -> unit) ->
  pos:('pos -> unit) ->
  ispos:bool -> env -> (bool * int) list -> ('neg, 'pos) typ -> unit =
  fun ~neg ~pos ~ispos env ext ty ->
  match ty with
  | Tsimple s -> pos s
  | Ttop _ -> ()
  | Tcons c ->
     Cons.map ~neg:(wf_typ ~neg:pos ~pos:neg ~ispos:(not ispos) env ext) ~pos:(wf_typ ~neg ~pos ~ispos env ext) c |> ignore
  | Tvar (_, v) -> wf_var env ext v
  | Tjoin (a, b) ->
     wf_typ ~neg ~pos ~ispos env ext a;
     wf_typ ~neg ~pos ~ispos env ext b
  | Tpoly {vars; body} ->
     let n_unique_vars = IArray.to_list vars |> List.map fst |> List.map fst |> List.sort_uniq String.compare |> List.length in
     assert (n_unique_vars = IArray.length vars);
     let ext = (ispos, IArray.length vars) :: ext in
     IArray.iter (fun (_, c) ->
       (* FIXME: constraints on c. Can it be e.g. Tsimple?
          Prob not same binder either. *)
       Option.iter (wf_typ ~neg:pos ~pos:neg ~ispos:(not ispos) env ext) c) vars;
     wf_typ ~neg ~pos ~ispos env ext body



(*
 * Unparsing: converting a typ back to a Exp.tyexp
 *)

let noloc : Location.t =
 { loc_start = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0};
   loc_end = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0} }

let mktyexp t = (Some t, noloc)

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, noloc)

let unparse_cons ~neg ~pos ty =
  let open Cons in
  let ty = match ty with
    | Bool -> named_type "bool"
    | Int -> named_type "int"
    | String -> named_type "string"
    | Record fs ->
       Trecord (Tuple_fields.map_fields (fun _ t -> pos t) fs)
    | Func (args, ret) ->
       Tfunc (Tuple_fields.map_fields (fun _ t -> neg t) args,
              pos ret) in
  mktyexp ty

let unparse_bound_var ~env:(_,ext) index var =
  let name =
    if index < List.length ext then
      IArray.get (List.nth ext index) var
    else
      match index - List.length ext with
      | 0 -> Printf.sprintf "$%d" var
      | n -> Printf.sprintf "$%d.%d" n var in
  mktyexp (named_type name)

let unparse_rigid_var ~env:(env,_) rv =
  let name =
    match env_rigid_var env rv with
    | rv ->
       (* FIXME: this name might be shadowed? *)
       fst rv.name
    | exception _ ->
       Printf.sprintf "##%d.%d" (Env_level.to_int rv.level) rv.var
  in
  mktyexp (named_type name)

let unparse_flexvar ~env:_ ~flexvar fv =
  flexvar fv;
  let name = flexvar_name fv in
  (* let name = Printf.sprintf "%s@%d" name (Env_level.to_int fv.level) in *)
  mktyexp (named_type name)

let unparse_var ~env = function
  | Vbound {index; var} -> unparse_bound_var ~env index var
  | Vrigid rv -> unparse_rigid_var ~env rv

let unparse_joins = function
  | [] -> mktyexp (named_type "nothing")
  | [x] -> x
  | x :: xs -> List.fold_left (fun a b -> mktyexp (Exp.Tjoin (a, b))) x xs

let rec unparse_gen_typ :
  'neg 'pos . env:(_ * _) -> neg:(env:(env*_) -> 'neg -> Exp.tyexp) -> pos:(env:(env*_) -> 'pos -> Exp.tyexp) ->
             ('neg,'pos) typ -> Exp.tyexp =
  fun ~env ~neg ~pos ty -> match ty with
  | Tsimple t -> pos ~env t
  | Ttop _ -> mktyexp (named_type "any")
  | Tcons c ->
     unparse_joins
       (List.map
         (unparse_cons ~neg:(unparse_gen_typ ~env ~neg:pos ~pos:neg) ~pos:(unparse_gen_typ ~env ~neg ~pos)) c.conses)
  | Tvar (_, var) ->
     unparse_var ~env var
  | Tjoin (a, b) ->
     mktyexp (Exp.Tjoin (unparse_gen_typ ~env ~neg ~pos a,
                         unparse_gen_typ ~env ~neg ~pos b))
  | Tpoly { vars; body } ->
     let env, bounds = unparse_bounds ~env ~neg ~pos vars in
     mktyexp (Exp.Tforall(bounds, unparse_gen_typ ~env ~neg ~pos body))

and unparse_bounds :
  'neg 'pos . env:_ -> neg:(env:(env*_) -> 'neg -> Exp.tyexp) -> pos:(env:(env*_) -> 'pos -> Exp.tyexp) ->
             (string Location.loc * ('pos,'neg) typ option) iarray -> _ * Exp.typolybounds =
  fun ~env:(env,ext) ~neg ~pos vars ->
  (* FIXME: this sort of freshening or shifts? *)
  (* FIXME: if freshening, use levels somehow to determine when not needed *)
  let taken name =
    lookup_named_type Location.noloc name <> None ||
    env_lookup_type_var env name <> None ||
    List.exists (fun names -> IArray.exists (String.equal name) names) ext in
  let rec freshen name i =
    let p = Printf.sprintf "%s_%d" name i in
    if not (taken p) then p else freshen name (i + 1) in
  let freshen name =
    if not (taken name) then name else freshen name 2 in
  let vars = IArray.map (fun ((s,l), b) -> (freshen s,l), b) vars in
  let ext = IArray.map (fun ((s,_),_) -> s) vars :: ext in
  (env,ext), IArray.map (fun ((s,_), bound) ->
       let s = (s, noloc) in
       match bound with
       | None | Some (Ttop _) ->
          s, None
       | Some t ->
          s, Some (unparse_gen_typ ~env:(env,ext) ~pos:neg ~neg:pos t)) vars |> IArray.to_list

let unparse_join = function
  | [] -> mktyexp (named_type "nothing")
  | t :: ts ->
     List.fold_left (fun a b -> mktyexp (Exp.Tjoin (a, b))) t ts

let rec unparse_flex_lower_bound ~env ~flexvar = function
  | Ltop _ ->
     mktyexp (named_type "any")
  | Lower(flexvars, {cons; rigvars}) ->
     let ts =
       List.map (unparse_flexvar ~env ~flexvar) (flexvars :> flexvar list)
       @
       List.map (unparse_cons ~neg:(unparse_flexvar ~env ~flexvar) ~pos:(unparse_flex_lower_bound ~env ~flexvar)) cons.conses
       @
       List.map (unparse_rigid_var ~env) (List.map fst (Rvset.to_list rigvars))
     in
     unparse_join ts

let unparse_styp_neg ~env ~flexvar = function
  | UBvar v -> unparse_flexvar ~env ~flexvar v
  | UBcons {cons;rigvars} ->
     unparse_join
       (List.map (unparse_cons ~neg:(unparse_flex_lower_bound ~env ~flexvar) ~pos:(unparse_flexvar ~env ~flexvar)) cons.conses
        @
        List.map (unparse_rigid_var ~env) (List.map fst (Rvset.to_list rigvars)))

let unparse_ptyp ~flexvar ?(env=(Env_nil,[])) (t : ptyp) =
  unparse_gen_typ ~env ~neg:(unparse_flexvar ~flexvar) ~pos:(unparse_flex_lower_bound ~flexvar) t
let unparse_ntyp ~flexvar ?(env=(Env_nil,[])) (t : ntyp) =
  unparse_gen_typ ~env ~neg:(unparse_flex_lower_bound ~flexvar) ~pos:(unparse_flexvar ~flexvar) t



(* For debugging *)
let pp_doc ppf doc =
  let buf = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. 10000 buf (PPrint.group doc);
  Format.fprintf ppf "%s" (Buffer.to_bytes buf |> Bytes.to_string)

let pp_tyexp ppf ty =
  let ty = Exp.map_tyexp Exp.normalise ty in
  pp_doc ppf (Print.tyexp ty)

let pp_exp ppf e =
  pp_doc ppf (Print.exp e)

let pp_flexlb ppf t =
  let doc = unparse_flex_lower_bound ~env:(Env_nil,[]) ~flexvar:ignore t in
  pp_tyexp ppf doc

let pp_styp_neg ppf t =
  let env = Env_nil, [] in
  let tys = List.map (unparse_styp_neg ~env ~flexvar:ignore) t in
  let docs = List.map (fun t -> Print.tyexp (Exp.map_tyexp Exp.normalise t)) tys in
  pp_doc ppf (PPrint.(separate (comma ^^ space) docs))

let pp_flexvar ppf v =
  let env = Env_nil, [] in
  pp_tyexp ppf (unparse_flexvar ~env ~flexvar:ignore v)

let pp_ntyp ppf t =
  let env = Env_nil, [] in
  pp_tyexp ppf (unparse_ntyp ~env ~flexvar:ignore t)

let pp_ptyp ppf t =
  let env = Env_nil, [] in
  pp_tyexp ppf (unparse_ptyp ~env ~flexvar:ignore t)

let dump_ptyp ppf t =
  let env = Env_nil, [] in
  let fvs = Hashtbl.create 20 in
  let fv_list = ref [] in
  let _name_ix = ref 0 in
  let rec flexvar fv =
    match Hashtbl.find fvs fv.id with
    | _ -> ()
    | exception Not_found ->
       let fv_name = flexvar_name fv in
       Hashtbl.add fvs fv.id (fv_name, None);
       fv_list := fv.id :: !fv_list;
       let l =
         if equal_flex_lower_bound fv.lower bottom then None
         else Some (unparse_flex_lower_bound ~env ~flexvar fv.lower) in
       let u = List.map (unparse_styp_neg ~env ~flexvar) fv.upper in
       Hashtbl.replace fvs fv.id (fv_name, Some (l, u));
       ()
  and unparse t =
    unparse_ptyp ~env ~flexvar t
  in
  let t = unparse t in
  let fvs = !fv_list |> List.rev |> List.map (fun i -> let (n, t) = (Hashtbl.find fvs i) in n, Option.get t) in
  Format.fprintf ppf "%a\n" pp_tyexp t;
  fvs |> List.iter (function
    | n, (l, us) ->
       begin match l with
       | Some l -> 
          Format.fprintf ppf " %a <= %s" pp_tyexp l n
       | None ->
          Format.fprintf ppf "      %s" n
       end;
       us |> List.iteri (fun i u ->
         Format.fprintf ppf "%s %a" (if i = 0 then " <=" else ";") pp_tyexp u);
       Format.fprintf ppf "\n")

let pp_changes ppf changes =
  Format.fprintf ppf "[";
  List.rev changes |> List.iteri (fun i ch ->
    let sp = if i = 0 then "" else " " in
    let pv fv ty =
      Format.fprintf ppf "%s%s%s" sp (flexvar_name fv) ty in
    match ch with
    | Change_expanded_mark -> Format.fprintf ppf "%s!" sp
    | Change_upper(v,_) -> pv v "-"
    | Change_lower(v,_) -> pv v "+"
(*    | Change_level(v,_) -> pv v "@"*));
  Format.fprintf ppf "]"


let wf_ptyp env (t : ptyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~neg:(wf_flexvar ~seen env (env_level env)) ~pos:(wf_flex_lower_bound ~seen env (env_level env)) ~ispos:true env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ptyp t

let wf_ntyp env (t : ntyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~neg:(wf_flex_lower_bound ~seen env (env_level env)) ~pos:(wf_flexvar ~seen env (env_level env)) ~ispos:false env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ntyp t
