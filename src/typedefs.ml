(*
 * Core definitions used by the typechecker
 *)
open Util
type 'a loc = 'a Location.loc

module StrMap = Map.Make (struct type t = string let compare = compare end)

module One_or_two = struct
  type ('a, 'b) t =
    | L of 'a
    | R of 'b
    | LR of 'a * 'b

  let left x = L x
  let right x = R x
  let both x y = LR (x,y)
end

module Fields = struct
  module Map = Tuple_fields.FieldMap
  module Table = Hashtbl.Make (struct
    type t = Tuple_fields.field_name
    let equal = Tuple_fields.equal_field_name
    let hash = Hashtbl.hash (*FIXME better hash*)
  end)

  type paloc = {pres_loc: Location.t; abs_loc: Location.t}
  type 'a field_desc =
    | Funknown of Location.t
    | Foptional of 'a * paloc
    | Fpresent of 'a loc
    | Fabsent of Location.t
    | Fbroken of paloc

  let equal_field_desc f p q =
    match p, q with
    | Funknown _, Funknown _ -> true
    | Foptional (p, _), Foptional (q, _) -> f p q
    | Fpresent (p, _), Fpresent (q, _) -> f p q
    | Fabsent _, Fabsent _ -> true
    | Fbroken _, Fbroken _ -> true
    | (Funknown _ | Foptional _ | Fpresent _ | Fabsent _ | Fbroken _), _ ->
       false

  let field_desc_map f = function
    | Foptional (x, l) -> Foptional (f x, l)
    | Fpresent (x, l) -> Fpresent (f x, l)
    | Funknown _ | Fabsent _ | Fbroken _ as f -> f

  let desc_of_ext l = function
    | Exp.Ext_open -> Funknown l
    | Exp.Ext_closed -> Fabsent l

  type 'a t =
    { fields: 'a field_desc Map.t;
      fnames: Tuple_fields.field_name list;
      fopen: Exp.extensible_flag }

  let equal ~pos
        {fields=pfields; fnames=pnames; fopen=popen}
        {fields=qfields; fnames=qnames; fopen=qopen} =
    pnames = qnames &&
    popen = qopen &&
    Map.equal (equal_field_desc pos) pfields qfields

  let map ~pos t =
    let fields = Map.map (field_desc_map pos) t.fields in
    { t with fields }

  let mapi ~pos t =
    let fields = Map.mapi (fun fn x -> field_desc_map (pos fn) x) t.fields in
    { t with fields }

  let wf ~pos {fields; fnames; fopen} =
    let remaining =
      List.fold_left (fun fields fn ->
        begin match Map.find fn fields with
        | Foptional (t, _) | Fpresent (t, _) -> pos t
        | _ -> ()
        | exception Not_found -> intfail "Cons.wf: missing field %s" (Tuple_fields.string_of_field_name fn)
        end;
        Map.remove fn fields) fields fnames in
    remaining |> Map.iter (fun _ d ->
      assert (equal_field_desc (fun _ _ -> false) d (desc_of_ext Location.noloc fopen)))

  let merge ~fdef ~f (a, a_loc) (b, b_loc) =
    let def_a = desc_of_ext a_loc a.fopen in
    let def_b = desc_of_ext b_loc b.fopen in
    let fopen = fdef a.fopen b.fopen in
    let def = desc_of_ext a_loc fopen in
    let is_default x = equal_field_desc (fun _ _ -> assert false) def x in
    assert (is_default (f def_a def_b));
    let seen = Table.create 10 in
    let merge_field fn a b =
      let r = f (Option.value a ~default:def_a) (Option.value b ~default:def_b) in
      if not (is_default r) then
        Table.add seen fn ();
      (* OPT: Consider dropping the field entirely if it's default with a_loc *)
      Some r
    in
    let fields = Map.merge merge_field a.fields b.fields in
    let check_name fn =
      if Table.mem seen fn
      then (Table.remove seen fn; true)
      else false
    in
    let fnames =
      let a_names = List.filter check_name a.fnames in
      let b_names = List.filter check_name b.fnames in
      a_names @ b_names
    in
    let r = { fields; fnames; fopen } in
    wf ~pos:ignore r; r

  let join ~pos a b =
    merge a b
      ~fdef:(fun a b -> match a, b with
          | Exp.Ext_closed, Exp.Ext_closed -> Exp.Ext_closed
          | _, _ -> Exp.Ext_open)
      ~f:(fun a b -> match a, b with
         | (Funknown _ as x), _
         | _, (Funknown _ as x) -> x
         | x, Fbroken _
         | Fbroken _, x -> x
         | Foptional (a, l), (Foptional (b, _) | Fpresent (b, _)) -> Foptional (pos a b, l)
         | Foptional _ as a, (Fabsent _) -> a
         | Fpresent (a, l), Fpresent (b, _) -> Fpresent (pos a b, l)
         | Fpresent (a, pres_loc), Foptional (b, l) ->
            Foptional (pos a b, {l with pres_loc})
         | Fpresent (a, pres_loc), Fabsent abs_loc ->
            Foptional (a, {abs_loc; pres_loc})
         | Fabsent abs_loc, (Foptional (b, {pres_loc; _})) ->
            Foptional (b, {abs_loc; pres_loc})
         | Fabsent _ as a, (Fabsent _) -> a
         | Fabsent abs_loc, Fpresent (b, pres_loc) ->
            Foptional (b, {abs_loc; pres_loc}))

  (* Meet. Locations from lower side, from left if same *)
  let meet ~pos a b =
    let open One_or_two in
    merge a b
      ~fdef:(fun a b -> match a, b with
          | Exp.Ext_open, Exp.Ext_open -> Exp.Ext_open
          | _, _ -> Exp.Ext_closed)
      ~f:(fun a b -> match a, b with
          | x, Funknown _ ->
             field_desc_map (fun x -> pos (L x)) x
          | Funknown _, x ->
             field_desc_map (fun x -> pos (R x)) x
          | (Fbroken _ as x), _
          | _, (Fbroken _ as x) -> x
          | Foptional (a, l), Foptional (b, _) ->
             Foptional (pos (LR (a, b)), l)
          | Foptional (a, _), Fpresent (b, l) ->
             Fpresent (pos (LR (a, b)), l)
          | Foptional _, (Fabsent _ as b) ->
             b
          | Fpresent (a, l), (Foptional (b, _) | Fpresent (b, _)) ->
             Fpresent (pos (LR (a, b)), l)
          | Fpresent (_, pres_loc), Fabsent abs_loc
          | Fabsent abs_loc, Fpresent (_, pres_loc) ->
             Fbroken {pres_loc; abs_loc}
          | (Fabsent _ as a), (Foptional _ | Fabsent _) ->
             a)

  let sub ~f (a,a_loc) (b,b_loc) =
    let def_a = desc_of_ext a_loc a.fopen in
    let def_b = desc_of_ext b_loc b.fopen in
    f None def_a def_b;
    let sub_field fn a b =
      f (Some fn) (Option.value a ~default:def_a) (Option.value b ~default:def_b);
      None
    in
    ignore (Map.merge sub_field a.fields b.fields)

  let of_list ~fopen fields =
    let fnames = List.map fst fields in
    let fields =
      List.fold_left (fun acc (f, x) -> Map.add f x acc) Map.empty fields
    in
    { fields; fnames; fopen }

  let to_list t =
    t.fnames |> List.map (fun f -> f, Map.find f t.fields)

  let find f (t, t_loc) =
    try Map.find f t.fields
    with Not_found -> desc_of_ext t_loc t.fopen

  let empty = { fopen = Ext_open; fnames = []; fields = Map.empty }
end

module Cons1 = struct
  open Fields
  type tuple_tag = string

  type (+'neg, +'pos) cons =
    | Top
    (* FIXME: maybe delete these once abstypes exist? *)
    | Bool
    | Int
    | String
    | Record of {
        tag: tuple_tag option;
        body: 'pos Fields.t
      }
    | Func of 'neg list * 'pos

  type (+'neg, +'pos) t = ('neg, 'pos) cons

  let equal ~neg ~pos p q =
    match p, q with
    | Top, Top -> true
    | Bool, Bool -> true
    | Int, Int -> true
    | String, String -> true
    | Record p, Record q ->
       Option.equal (String.equal) p.tag q.tag &&
       Fields.equal ~pos p.body q.body
    | Func (pa, pr), Func (qa, qr) ->
       List.equal neg pa qa &&
       pos pr qr
    | (Bool|Int|String|Record _|Func _|Top), _ -> false

  let map ~neg ~pos = function
    | Top -> Top
    | Bool -> Bool
    | Int -> Int
    | String -> String
    | Record {tag; body} ->
       Record {tag; body = Fields.map ~pos body}
    | Func (args, res) ->
       let args = List.map neg args in
       let res = pos res in
       Func (args, res)

  let wf ~neg ~pos = function
    | Top | Bool | Int | String -> ()
    | Record {tag=_; body} ->
       Fields.wf ~pos body
    | Func (args, res) ->
       List.iter neg args;
       pos res

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
    | Record {tag; body} ->
       let pos fn x = pos (Record_field fn) x in
       Record {tag; body = Fields.mapi ~pos body }
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
    | Id, c -> c
    | To_top, _ -> Top
    | Drop_record_tag t, Record {tag=Some t'; body} ->
       assert (t = t');
       Record {tag=None; body}
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

    | Record {tag=ptag; _}, Record {tag=qtag; _} ->
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

  let join ~neg ~pos (a, a_loc) (b, b_loc) =
    assert (sub_head a b = Le Id);
    match a, b with
    | Top, Top -> Top, a_loc
    | (Top, _) | (_, Top) -> assert false

    | Bool, Bool -> Bool, a_loc
    | Int, Int -> Int, a_loc
    | String, String -> String, a_loc
    | (Bool|Int|String), _ | _, (Bool|Int|String) ->
       assert false

    | Record a, Record b ->
       assert (a.tag = b.tag);
       Record {tag = a.tag; body = Fields.join ~pos (a.body, a_loc) (b.body, b_loc) },
       a_loc (* FIXME: which loc is best here? *)

    | Func (args, res), Func (args', res') ->
       let args = List.map2 neg args args' in
       Func(args, pos res res'), a_loc

    | Record _, Func _ | Func _, Record _ -> assert false

  let meet ~neg ~pos (a, a_loc) (b, b_loc) =
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
    | Record a, Record b ->
       let tag =
         match a.tag, b.tag with
         | None, x | x, None -> x
         | Some t, Some t' -> assert (t = t'); a.tag
       in
       Record {tag; body = Fields.meet ~pos (a.body, a_loc) (b.body, b_loc) }
    | Func (args, res), Func (args', res') ->
       let args =
         List.map2 (fun x y -> neg (LR (x,y))) args args' in
       let res = pos (LR (res, res')) in
       Func (args, res)
    | Record _, Func _ | Func _, Record _ -> assert false

  type field_error =
    | Field_missing of Tuple_fields.field_name * Location.t * Location.t
    | Field_extra of Tuple_fields.field_name option * Location.t * Location.t

  exception SubError of field_error

  let sub ~neg ~pos (a, a_loc) (b, b_loc) =
    assert (sub_head a b = Le Id);
    match a, b with
    | Top, Top
    | Bool, Bool
    | Int, Int
    | String, String -> Ok ()
    | Func (args, res), Func (args', res') ->
       List.combine args' args
       |> List.iteri (fun i (a', a) -> neg (Func_arg i) a' a);
       pos Func_res res res';
       Ok ()
    | Record a, Record b ->
       assert (a.tag = b.tag);
       let sub_field k a b =
         match a, b with
         | _, Funknown _ -> ()
         | Fbroken _, _ -> ()
         | Fabsent _, (Fabsent _ | Foptional _) -> ()
         | (Foptional (a, _) | Fpresent (a, _)), Foptional (b, _)
         | Fpresent (a, _), Fpresent (b, _) -> pos (Record_field (Option.get k)) a b

         | (Funknown la | Fabsent la | Foptional (_, {abs_loc=la; _})),
           (Fpresent (_, lb) | Fbroken {pres_loc=lb; _})
         | (Funknown la, Foptional (_, {pres_loc=lb; _})) ->
            (* failed to be present *)
            raise (SubError (Field_missing (Option.get k, la, lb)))
         | (Funknown la | Foptional (_,{pres_loc=la;_}) | Fpresent (_, la)),
           (Fbroken {abs_loc=lb;_} | Fabsent lb) ->
            (* failed to be absent *)
            raise (SubError (Field_extra (k, la, lb)))
       in
       begin match Fields.sub ~f:sub_field (a.body,a_loc) (b.body,b_loc) with
       | () -> Ok ()
       | exception (SubError e) -> Error e
       end
    | _ -> assert false

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
     Cons1.wf ~neg:(assert_locally_closed ix) ~pos:(assert_locally_closed ix) c
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
    | Lcons (c,_) -> Cons1.wf ~neg:(wf_flexvar ~seen env lvl) ~pos:(wf_lower ~seen env lvl) c)

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
     Cons1.wf ~neg:(wf_typ ~neg:pos ~pos:neg ~ispos:(not ispos) env ext) ~pos:(wf_typ ~neg ~pos ~ispos env ext) c
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

let mktyexp t = (Some t, Location.noloc)

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, Location.noloc)

let unparse_cons ~neg ~pos (ty,_tyloc) =
  let open Cons1 in
  let ty = match ty with
    | Top -> named_type "any"
    | Bool -> named_type "bool"
    | Int -> named_type "int"
    | String -> named_type "string"
    | Record {tag; body = {fields; fnames; fopen}} ->
       let open Fields in
       let unparse_field_desc k = function
         | Funknown l -> (k,l), Exp.Optional, None
         | Foptional (a, l) -> (k,l.pres_loc), Exp.Optional, Some (pos a)
         | Fpresent (a, l) -> (k,l), Exp.Mandatory, Some (pos a)
         | Fabsent l -> (k,l), Exp.Optional, Some (mktyexp (named_type "absent"))
         | Fbroken l -> (k,l.abs_loc), Exp.Mandatory, Some (mktyexp (named_type "absent"))
       in
       let fs =
         match
           List.mapi (fun i f ->
             match f with
             | Tuple_fields.Field_positional j when i = j ->
                begin match Map.find f fields with
                | Fpresent (a,_loc) -> pos a
                | _ -> raise_notrace Exit
                end
             | _ -> raise_notrace Exit)
             fnames
         with
         | tuple ->
            Exp.Ftuple (tuple, fopen)
         | exception Exit ->
            Exp.Frecord (List.map (fun f -> unparse_field_desc f (Map.find f fields)) fnames,
                         fopen)
       in
       Trecord (Option.map (fun t -> t, Location.noloc) tag, fs)
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
       let s = (s, Location.noloc) in
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
