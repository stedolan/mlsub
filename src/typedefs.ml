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

module One_or_two = struct
  type ('a, 'b) t =
    | L of 'a
    | R of 'b
    | LR of 'a * 'b

  let left x = L x
  let right x = R x
  let both x y = LR (x,y)
end

module Cons1 = struct
  type tuple_tag = string
  type (+'neg, +'pos) cons =
    | Top
    (* FIXME: maybe delete these once abstypes exist? *)
    | Bool
    | Int
    | String
    (* FIXME: add a loc to tuple tag and each field *)
    | Record of tuple_tag option * 'pos Tuple_fields.tuple_fields
    | Func of 'neg list * 'pos

  type (+'neg, +'pos) t = ('neg, 'pos) cons

  let equal ~neg ~pos p q =
    match p, q with
    | Top, Top -> true
    | Bool, Bool -> true
    | Int, Int -> true
    | String, String -> true
    | Record (pt, p), Record (qt, q) ->
       Option.equal (String.equal) pt qt &&
       Tuple_fields.equal_fields pos p q
    | Func (pa, pr), Func (qa, qr) ->
       List.equal neg pa qa &&
       pos pr qr
    | (Bool|Int|String|Record _|Func _|Top), _ -> false

  let map ~neg ~pos = function
    | Top -> Top
    | Bool -> Bool
    | Int -> Int
    | String -> String
    | Record (tag,fields) ->
       Record (tag, Tuple_fields.map_fields (fun _fn x -> pos x) fields)
    | Func (args, res) ->
       let args = List.map neg args in
       let res = pos res in
       Func (args, res)

  let iter ~neg ~pos x = ignore (map ~neg ~pos x)

  type field =
    | Func_arg of int
    | Func_res
    | Record_field of Tuple_fields.field_name

  let field_is_positive = function
    | Func_arg _ -> false
    | Func_res | Record_field _ -> true

  let equal_field a b =
    match a, b with
    | Func_arg i, Func_arg j -> i = j
    | Func_res, Func_res -> true
    | Record_field a, Record_field b ->
       Tuple_fields.equal_field_name a b
    | _ -> false

  let mapi ~neg ~pos = function
    | Top -> Top
    | Bool -> Bool
    | Int -> Int
    | String -> String
    | Record (tag,fields) ->
       Record (tag, Tuple_fields.map_fields (fun fn x -> pos (Record_field fn) x) fields)
    | Func (args, res) ->
       let args = List.mapi (fun i x -> neg (Func_arg i) x) args in
       let res = pos Func_res res in
       Func (args, res)

  type head_coercion =
    | Id
    | Drop_record_tag of tuple_tag
    | To_top

  type head_conflict =
    | Incompatible
    | Args of [`Too_few | `Too_many | `Wrong_number]
    | Expected_tag of (tuple_tag option * tuple_tag list)

  let merge_head_conflicts xs =
    let merge c d =
      match c, d with
      | Incompatible, x | x, Incompatible -> x
      | Args c, Args d ->
         if c = d then Args c else Args `Wrong_number
      | Args _, _ | _, Args _ -> Incompatible
      | Expected_tag (p, c), Expected_tag (q, d) ->
         Expected_tag ((if p = q then p else None), c @ d)
    in
    List.fold_left merge Incompatible xs

  (* least c' greater than c along coe *)
  let coerce_up coe c =
    match coe, c with
    | Id, c ->
       c
    | To_top, _ -> Top
    | Drop_record_tag t, Record (Some t', fs) ->
       assert (t = t');
       Record (None, fs)
    | Drop_record_tag _, _ -> assert false

  type head_ordering =
    | Un of head_conflict
    | Le of head_coercion

  let sub_head p q =
    match p, q with
    | Top, Top -> Le Id
    | _, Top -> Le To_top
    | Top, _ -> Un Incompatible
    | Bool, Bool -> Le Id
    | Int, Int -> Le Id
    | String, String -> Le Id
    | (Bool|Int|String), _
    | _, (Bool|Int|String) -> Un Incompatible

    | Func (pa, _), Func (qa, _) ->
       begin match List.compare_lengths pa qa with
       | 0 -> Le Id
       | n -> Un (Args (if n > 0 then `Too_few else `Too_many))
       end
    | Func _, _
    | _, Func _ -> Un Incompatible

    | Record (ptag, _), Record (qtag, _) ->
       begin match ptag, qtag with
       | None, None -> Le Id
       | Some t, None -> Le (Drop_record_tag t)
       | Some pt, Some qt when String.equal pt qt -> Le Id
       | _, Some qt -> Un (Expected_tag (ptag, [qt]))
       end

  let incomparable_head a b =
    match sub_head a b, sub_head b a with
    | Un _, Un _ -> true
    | _, _ -> false

  let join ~neg ~pos a b =
    assert (sub_head a b = Le Id);
    match a, b with
    | Top, Top -> Top
    | (Top, _) | (_, Top) -> assert false

    | Bool, Bool -> Bool
    | Int, Int -> Int
    | String, String -> String
    | (Bool|Int|String), _ | _, (Bool|Int|String) ->
       assert false

    | Record (tag, c), Record (tag', c') ->
       assert (tag = tag');
       let fields =
         Tuple_fields.inter c c'
           ~both:(fun s t -> pos s t)
       in
       Record (tag, fields)

    | Func (args, res), Func (args', res') ->
       let args = List.map2 neg args args' in
       Func(args, pos res res')

    | Record _, Func _ | Func _, Record _ -> assert false

  let meet ~neg ~pos a b =
    (* tree heads means meet exists only for comparable heads *)
    assert (not (incomparable_head a b));
    let open One_or_two in
    match a, b with
    | Top, x ->
       map ~neg:(fun x -> neg (R x)) ~pos:(fun x -> pos (R x)) x
    | x, Top ->
       map ~neg:(fun x -> neg (L x)) ~pos:(fun x -> pos (L x)) x
    | Bool, Bool -> Bool
    | Int, Int -> Int
    | String, String -> String
    | (Bool|Int|String), _ | _, (Bool|Int|String) ->
       assert false
    | Record (tag, c), Record (tag', c') ->
       let tag =
         match tag, tag' with
         | None, x | x, None -> x
         | Some t, Some t' -> assert (t = t'); tag
       in
       (* FIXME hack until better closed/open logic is implemented. Wrong here! *)
       let fields =
         Tuple_fields.merge_fields c c'
           ~left:(fun _ x -> Some (pos (L x)))
           ~right:(fun _ y -> Some (pos (R y)))
           ~both:(fun _ x y -> Some (pos (LR (x, y))))
           ~extra:(function (`Open,_), (`Open,_) -> `Open | _ -> `Closed (* Unsound! *))
       in
       Record(tag, fields)
    | Func (args, res), Func (args', res') ->
       let args =
         List.map2 (fun x y -> neg (LR (x,y))) args args' in
       let res = pos (LR (res, res')) in
       Func (args, res)
    | Record _, Func _ | Func _, Record _ -> assert false

  type sub_error =
    | Field_missing of Tuple_fields.field_name
    | Field_extra of Tuple_fields.field_name option

  exception SubError of sub_error

  let sub ~neg ~pos a b =
    assert (sub_head a b = Le Id);
    match
      match a, b with
      | Top, Top
      | Bool, Bool
      | Int, Int
      | String, String -> ()
      | Func (args, res), Func (args', res') ->
         List.combine args' args
         |> List.iteri (fun i (a', a) -> neg (Func_arg i) a' a);
         pos Func_res res res';
         ()
      | Record (t, af), Record (t', bf) ->
         assert (t = t');
         let open Tuple_fields in
         begin match bf.fopen, af.fopen with
         | `Open, _ ->  ()
         | `Closed, `Open -> raise (SubError (Field_extra None))
         | `Closed, `Closed ->
            match List.find_opt (fun k -> not (FieldMap.mem k bf.fields)) af.fnames with
            | Some k -> raise (SubError (Field_extra (Some k)))
            | None -> ()
         end;
         FieldMap.bindings bf.fields |> List.iter (fun (k, b) ->
           match FieldMap.find k af.fields with
           | exception Not_found -> raise (SubError (Field_missing k))
           | a -> pos (Record_field k) a b);
      | _ -> assert false
    with
    | () -> Ok ()
    | exception (SubError e) -> Error e

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
    var: int;
    loc: Location.t }

let equal_rigvar (p : rigvar) (q : rigvar) =
  Env_level.equal p.level q.level && p.var = q.var

(* Flexvars are mutable but only in one direction.
     - level may decrease
     - bounds may become tighter (upper decreases, lower increases) *)
type flexvar =
  { level: env_level;
    id: int;    (* for printing/sorting *)
    mutable upper: upper;
    mutable lower: lower;
    mutable gen: flexvar_gen;
  }

and lower = lower_part list


(* Matchability constraint: the contravariant parts of a flexible variable's lower bound must be flexible variables.
   Flexible variables appearing in vars must not have UBvar upper bounds, as they are also constrained above here.
   Flexible variables appearing negatively in ctor might well have UBvar upper bounds.
 *)
and lower_part =
  | Lflexvar of flexvar
  | Lrigvar of rigvar
  | Lcons of (flexvar, lower) Cons1.t Location.loc

and upper =
  | Utop  (* Unrotated equiv of Ugen {cons=Top; higher_fvs=[]} *)
  | Uflexvar of flexvar
  | Ugen of
      { cons: (lower, flexvar) upper_cons Location.loc;
        higher_fvs: flexvar list }

and (+'neg,+'pos) upper_cons = ('neg,'pos) upper_part list

and (+'neg,+'pos) upper_part =
  | Urigvar of rigvar * delayed_constraint list
  | Ucons of ('neg, 'pos) Cons1.t

and delayed_constraint =
  { dy_lower: lower;
    dy_upper: upper;
    dy_flexvar: flexvar;
    mutable dy_resolved: bool }


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

(* Variables in typs *)
type typ_var =
  | Vbound of {index: int; var:int; loc: Location.t}
  | Vrigid of rigvar

(* FIXME: enforce tjoin invariants, especially in neg types *)
type (+'neg, +'pos) typ =
  | Tsimple of 'pos
  (* Top is a Tcons but Bot has a special repr *)
  | Tbot of Location.t option
  | Tcons of ('neg, 'pos) cons_typ
  | Tvar of typ_var
  | Tjoin of ('neg, 'pos) typ * ('neg, 'pos) typ * Location.t option
     (* No Tpoly allowed under a Tjoin *)
  | Tpoly of ('neg, 'pos) poly_typ
and (+'neg, +'pos) cons_typ = (('pos, 'neg) typ, ('neg, 'pos) typ) Cons1.t Location.loc
and (+'neg, +'pos) poly_typ =
  { (* names must be distinct *)
    (* bound must be a constructed type, possibly joined with some rigid/bound vars *)
    vars : (string Location.loc * ('pos, 'neg) typ option) iarray;
    body : ('neg, 'pos) typ }

type ptyp = (flexvar, lower) typ
type ntyp = (lower, flexvar) typ

type gen_level = env_level option

type value_binding =
  { typ: ptyp;
    (* The level of the outermost unannotated lambda-bound parameter
       reachable from this binding by expanding untyped let definitions.
       (cf. Haskell's MonoLocalBinds) *)
    gen_level: gen_level;
    comp_var: IR.value IR.Binder.ref
  }

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
  upper : (flexvar, lower) Cons1.t list;
}

(*
 * Equality checks (Syntactic, not subtyping-aware, ignore locations)
 *)

let equal_flexvar (p : flexvar) (q : flexvar) =
  p == q

let rec equal_lower (p : lower) (q : lower) =
  let eq p q =
    match p, q with
    | Lflexvar pv, Lflexvar qv -> equal_flexvar pv qv
    | Lrigvar pv, Lrigvar qv -> equal_rigvar pv qv
    | Lcons (pc, _), Lcons (qc, _) -> Cons1.equal ~neg:equal_flexvar ~pos:equal_lower pc qc
    | _, _ -> false
  in List.equal eq p q

let equal_upper_cons_loc ((p,_) : _ upper_cons Location.loc) ((q,_) : _ upper_cons Location.loc) =
  let eq p q =
    match p, q with
    | Urigvar (pv, _pds_FIXME), Urigvar (qv, _qds_FIXME) -> equal_rigvar pv qv
    | Ucons pc, Ucons qc ->
       Cons1.equal pc qc ~neg:equal_lower ~pos:equal_flexvar
    | _, _ -> false
  in
  List.equal eq p q

let equal_upper (p : upper) (q : upper) =
  match p, q with
  | Utop, Utop -> true
  | Uflexvar pv, Uflexvar qv -> equal_flexvar pv qv
  | Ugen {cons=pc; higher_fvs=pv},
    Ugen {cons=qc; higher_fvs=qv} ->
     equal_upper_cons_loc pc qc &&
     List.equal equal_flexvar pv qv
  | _, _ -> false

let bottom : lower = []
let of_flexvar fv = [Lflexvar fv]
let of_rigvar rv = [Lrigvar rv]
let is_bottom = function [] -> true | _ -> false

(*
 * Flexvar mutations and backtracking log
 *)

type flexvar_change =
  | Change_expanded_mark (* hack for logging expand changes *)
  | Change_upper of flexvar * upper
  | Change_lower of flexvar * lower

let fv_set_upper ~changes fv upper =
  changes := Change_upper (fv, fv.upper) :: !changes;
  fv.upper <- upper

let fv_set_lower ~changes fv lower =
  assert (lower |> List.for_all (function Lflexvar fv' -> not (equal_flexvar fv fv') | _ -> true));
  changes := Change_lower (fv, fv.lower) :: !changes;
  fv.lower <- lower

let fv_maybe_set_lower ~changes fv lower =
  if not (equal_lower fv.lower lower) then
    (fv_set_lower ~changes fv lower; true)
  else false

let fv_maybe_set_upper ~changes (fv : flexvar) upper =
  if not (equal_upper fv.upper upper) then
    (fv_set_upper ~changes fv upper; true)
  else false

let revert changes =
  changes |> List.iter (function
  | Change_expanded_mark -> ()
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
  | Tsimple _ | Tbot _ -> ()
  | Tcons (c, _cloc) ->
     Cons1.iter ~neg:(assert_locally_closed ix) ~pos:(assert_locally_closed ix) c
  | Tvar v -> assert_locally_closed_var ix v
  | Tjoin (a, b, _loc) -> assert_locally_closed ix a; assert_locally_closed ix b
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     vars |> IArray.iter (fun (_, b) -> Option.iter (assert_locally_closed ix) b);
     assert_locally_closed ix body

let open_typ_var f ix = function
  | Vbound {index; var; loc} when index >= ix ->
     assert (index = ix);
     let res = f loc var in
     assert_locally_closed ix res;
     res
  | v -> Tvar v

let rec open_typ :
  'neg 'pos .
    neg:(Location.t -> int -> ('pos, 'neg) typ) ->
    pos:(Location.t -> int -> ('neg, 'pos) typ) ->
    int -> ('neg, 'pos) typ -> ('neg, 'pos) typ =
  fun ~neg ~pos ix t -> match t with
  | (Tsimple _ | Tbot _) as s -> s
  | Tcons (c, cloc) ->
     Tcons (Cons1.map ~neg:(open_typ ~neg:pos ~pos:neg ix) ~pos:(open_typ ~neg ~pos ix) c, cloc)
  | Tvar v -> open_typ_var pos ix v
  | Tjoin (a,b,loc) -> Tjoin (open_typ ~neg ~pos ix a, open_typ ~neg ~pos ix b, loc)
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, Option.map (open_typ ~neg:pos ~pos:neg ix) b) vars;
            body = open_typ ~neg ~pos ix body}

let close_typ_var lvl f ~ispos ~isjoin index = function
  | Vrigid {level; loc; _} as v when Env_level.equal lvl level ->
     Vbound {index; var = f v ~ispos ~isjoin; loc}
  | v -> v

(* Can only be used on typs without Tsimple nodes.
   (This limits it to use during parsing, which does not generate Tsimple) *)
let rec close_typ :
  'a 'b . env_level -> (typ_var -> ispos:bool -> isjoin:bool -> int) -> simple:('a -> 'b)  -> ispos:bool -> isjoin:bool -> int -> ('a, 'a) typ -> ('b, 'b) typ
  = fun lvl var ~simple ~ispos ~isjoin ix ty -> match ty with
  | Tsimple z -> Tsimple (simple z)
  | Tbot _ as z -> z
  | Tcons (c, cloc) -> Tcons (Cons1.map ~neg:(close_typ lvl var ~simple ~ispos:(not ispos) ~isjoin:false ix) ~pos:(close_typ lvl var ~simple ~ispos ~isjoin:false ix) c, cloc)
  | Tvar v -> Tvar (close_typ_var lvl var ~ispos ~isjoin ix v)
  | Tjoin (a, b, loc) ->
     Tjoin(close_typ lvl var ~simple ~ispos ~isjoin:true ix a,
           close_typ lvl var ~simple ~ispos ~isjoin:true ix b,
           loc)
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
  { level; upper = Utop; lower = bottom; id; gen = Not_generalising }


let rec env_lookup_type_var env loc name : rigvar option =
  match env with
  | Env_vals vs -> env_lookup_type_var vs.rest loc name
  | Env_types ts ->
     begin match SymMap.find name ts.rig_names with
     | var -> Some {level = ts.level; var; loc}
     | exception Not_found -> env_lookup_type_var ts.rest loc name
     end
  | Env_nil -> None

let lookup_named_type loc = function
  | "any" -> Some (Tcons (Top, loc))
  | "nothing" -> Some (Tbot (Some loc))
  | "bool" -> Some (Tcons (Bool, loc))
  | "int" -> Some (Tcons (Int, loc))
  | "string" -> Some (Tcons (String, loc))
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
  assert (not (List.exists (function Lflexvar v -> equal_flexvar v fv | _ -> false) fv.lower));
  wf_lower ~seen env fv.level fv.lower;
  wf_upper ~seen env fv.level fv.upper
  end

and wf_upper ~seen env lvl = function
  | Utop -> ()
  | Uflexvar v -> wf_flexvar ~seen env lvl v
  | Ugen {cons=(cons,_loc); higher_fvs} ->
     higher_fvs |> List.iter (fun v ->
       assert (not (Env_level.equal lvl v.level));
       wf_flexvar ~seen env lvl v);
       cons |> List.iter (function
         | Urigvar (rv, ds) ->
            wf_rigvar env lvl rv;
            List.iter (wf_delayed_constraint ~seen env lvl) ds
         | Ucons c ->
            Cons1.map c
              ~neg:(wf_lower ~seen env lvl)
              ~pos:(wf_flexvar ~seen env lvl)
            |> ignore);
       cons |> List.iteri (fun i c ->
         cons |> List.iteri (fun j d ->
           if i < j then match c, d with
           | Urigvar (a,_), Urigvar (b,_) -> assert (not (equal_rigvar a b))
           | Ucons a, Ucons b -> assert (Cons1.incomparable_head a b)
           | _, _ -> ()))

and wf_delayed_constraint ~seen env _lvl {dy_lower; dy_upper; dy_flexvar; dy_resolved=_} =
  wf_lower ~seen env dy_flexvar.level dy_lower;
  wf_upper ~seen env dy_flexvar.level dy_upper

and wf_rigvar env lvl (rv : rigvar) =
  assert (Env_level.extends rv.level lvl);
  let rvs = env_rigid_vars env rv.level in
  assert (0 <= rv.var && rv.var < IArray.length rvs)

and wf_lower ~seen env lvl l =
  l |> List.iteri (fun i a ->
    l |> List.iteri (fun j b ->
      if i < j then match a, b with
      | Lflexvar a, Lflexvar b -> assert (not (equal_flexvar a b))
      | Lrigvar a, Lrigvar b -> assert (not (equal_rigvar a b))
      | Lcons (a,_), Lcons (b,_) -> assert (Cons1.incomparable_head a b)
      | _, _ -> ()));
  l |> List.iter (function
    | Lflexvar v -> wf_flexvar ~seen env lvl v
    | Lrigvar v -> wf_rigvar env lvl v
    | Lcons (c,_) -> Cons1.iter ~neg:(wf_flexvar ~seen env lvl) ~pos:(wf_lower ~seen env lvl) c)

let wf_var env ext = function
  | Vrigid rv -> wf_rigvar env rv.level rv
  | Vbound {index; var; loc=_} ->
     assert (0 <= index && index < List.length ext);
     assert (0 <= var && var < snd (List.nth ext index))

let rec wf_typ : 'pos 'neg .
  neg:('neg -> unit) ->
  pos:('pos -> unit) ->
  ispos:bool -> env -> (bool * int) list -> ('neg, 'pos) typ -> unit =
  fun ~neg ~pos ~ispos env ext ty ->
  match ty with
  | Tsimple s -> pos s
  | Tbot _  -> ()
  | Tcons (c, _cloc) ->
     Cons1.iter ~neg:(wf_typ ~neg:pos ~pos:neg ~ispos:(not ispos) env ext) ~pos:(wf_typ ~neg ~pos ~ispos env ext) c
  | Tvar v -> wf_var env ext v
  | Tjoin (a, b, _loc) ->
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
 [{ loc_start = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0};
    loc_end = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0} }]

let mktyexp t = (Some t, noloc)

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, noloc)

let unparse_cons ~neg ~pos (ty,_tyloc) =
  let open Cons1 in
  let ty = match ty with
    | Top -> named_type "any"
    | Bool -> named_type "bool"
    | Int -> named_type "int"
    | String -> named_type "string"
    | Record (tag, fs) ->
       Trecord (Option.map (fun t -> t, noloc) tag,
                Tuple_fields.map_fields (fun _ t -> pos t) fs)
    | Func (args, ret) ->
       Tfunc (List.map neg args, pos ret)
  in
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
  | Vbound {index; var; loc=_} -> unparse_bound_var ~env index var
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
  | Tbot _ -> mktyexp (named_type "nothing")
  | Tcons c ->
     unparse_cons ~neg:(unparse_gen_typ ~env ~neg:pos ~pos:neg) ~pos:(unparse_gen_typ ~env ~neg ~pos) c
  | Tvar var ->
     unparse_var ~env var
  | Tjoin (a, b, _loc) ->
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
    env_lookup_type_var env Location.noloc name <> None ||
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
       | None | Some (Tcons (Top, _)) ->
          s, None
       | Some t ->
          s, Some (unparse_gen_typ ~env:(env,ext) ~pos:neg ~neg:pos t)) vars |> IArray.to_list

let unparse_join = function
  | [] -> mktyexp (named_type "nothing")
  | t :: ts ->
     List.fold_left (fun a b -> mktyexp (Exp.Tjoin (a, b))) t ts

let rec unparse_lower ~env ~flexvar l =
  l
  |> List.map (function
    | Lflexvar fv -> unparse_flexvar ~env ~flexvar fv
    | Lrigvar rv -> unparse_rigid_var ~env rv
    | Lcons c -> unparse_cons c ~neg:(unparse_flexvar ~env ~flexvar) ~pos:(unparse_lower ~env ~flexvar))
  |> unparse_join

let unparse_upper ~env ~flexvar = function
  | Utop -> []
  | Uflexvar v -> [unparse_flexvar ~env ~flexvar v]
  | Ugen {cons=([Ucons Top], _loc); higher_fvs=[]} -> []
  | Ugen {cons=(cons,_loc); higher_fvs} ->
     (   (* FIXME: do something with delayed constraints? *)
         [unparse_join
           (cons |> List.map (fun c -> match c with
              | Urigvar (rv, _FIXME) -> unparse_rigid_var ~env rv
              | Ucons c -> unparse_cons ~neg:(unparse_lower ~env ~flexvar) ~pos:(unparse_flexvar ~env ~flexvar) (c,())))])
     @ List.map (unparse_flexvar ~env ~flexvar) higher_fvs

let unparse_ptyp ~flexvar ?(env=(Env_nil,[])) (t : ptyp) =
  unparse_gen_typ ~env ~neg:(unparse_flexvar ~flexvar) ~pos:(unparse_lower ~flexvar) t
let unparse_ntyp ~flexvar ?(env=(Env_nil,[])) (t : ntyp) =
  unparse_gen_typ ~env ~neg:(unparse_lower ~flexvar) ~pos:(unparse_flexvar ~flexvar) t



(* For debugging *)
let pp_doc ppf doc =
  let buf = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. 10000 buf (PPrint.group doc);
  Format.fprintf ppf "%s" (Buffer.to_bytes buf |> Bytes.to_string)

let pp_tyexp ppf ty =
  pp_doc ppf (Print.tyexp ty)

let pp_exp ppf e =
  pp_doc ppf (Print.exp e)

let pp_flexlb ppf t =
  let doc = unparse_lower ~env:(Env_nil,[]) ~flexvar:ignore t in
  pp_tyexp ppf doc

let pp_upper ppf t =
  let env = Env_nil, [] in
  let tys = unparse_upper ~env ~flexvar:ignore t in
  let docs = List.map Print.tyexp tys in
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
         if equal_lower fv.lower bottom then None
         else Some (unparse_lower ~env ~flexvar fv.lower) in
       let u = unparse_upper ~env ~flexvar fv.upper in
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
    | Change_lower(v,_) -> pv v "+");
  Format.fprintf ppf "]"


let wf_ptyp env (t : ptyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~neg:(wf_flexvar ~seen env (env_level env)) ~pos:(wf_lower ~seen env (env_level env)) ~ispos:true env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ptyp t

let wf_ntyp env (t : ntyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~neg:(wf_lower ~seen env (env_level env)) ~pos:(wf_flexvar ~seen env (env_level env)) ~ispos:false env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ntyp t
