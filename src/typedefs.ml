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
      fnames: Tuple_fields.field_name list }

  let equal ~pos
        {fields=pfields; fnames=pnames}
        {fields=qfields; fnames=qnames} =
    pnames = qnames &&
    Map.equal (equal_field_desc pos) pfields qfields

  let map ~pos t =
    let fields = Map.map (field_desc_map pos) t.fields in
    { t with fields }

  let mapi ~pos t =
    let fields = Map.mapi (fun fn x -> field_desc_map (pos fn) x) t.fields in
    { t with fields }

  let mapi_desc ~pos t =
    let fields = Map.mapi (fun fn x -> pos fn x) t.fields in
    { t with fields }

  let filter_map ~pos {fnames; fields} =
    let fnames, fields =
      List.fold_left
        (fun (names, acc) fn ->
          let x =
            match field_desc_map pos (Map.find fn fields) with
            | Fpresent (Some x, l) -> Some (Fpresent (x, l))
            | Foptional (Some x, l) -> Some (Foptional (x, l))
            | Fpresent (None, _) | Foptional (None, _) -> None
            | (Fbroken _ | Fabsent _ | Funknown _) -> None
          in
          match x with
          | None -> names, acc
          | Some x -> fn :: names, Map.add fn x acc)
        ([], Map.empty)
        fnames
    in
    { fnames = List.rev fnames; fields }

  let wf ~pos {fields; fnames} =
    let remaining =
      List.fold_left (fun fields fn ->
        begin match Map.find fn fields with
        | Foptional (t, _) | Fpresent (t, _) -> pos t
        | _ -> ()
        | exception Not_found -> intfail "Cons.wf: missing field %s" (Tuple_fields.string_of_field_name fn)
        end;
        Map.remove fn fields) fields fnames in
    remaining |> Map.iter (fun _ d ->
      match d with
      | Funknown _ | Fabsent _ -> ()
      | _ -> assert false)

  let of_list fields =
    let fnames = List.map fst fields in
    let fields =
      List.fold_left (fun acc (f, x) -> Map.add f x acc) Map.empty fields
    in
    { fields; fnames }

  let to_list t =
    t.fnames |> List.map (fun f -> f, Map.find f t.fields)

  let find f (t, _t_loc) =
    Map.find_opt f t.fields

  let empty = { fnames = []; fields = Map.empty }

  let is_empty = function
    | { fnames = []; fields = _ } -> true
    | _ -> false

  let mem f t = Map.mem f t.fields
end

module Cons1 = struct
  (* FIXME: add the None case here? *)
  type tuple_tag = Exp.tuple_tag =
    | Anon_tag
    | Struct_tag of string loc
    | Named_tag of Exp.symbol

  let tuple_tag_equal a b =
    match a, b with
    | Anon_tag, Anon_tag -> true
    | Struct_tag (a,_), Struct_tag (b,_) -> String.equal a b
    | Named_tag (a,_), Named_tag (b,_) -> String.equal a b
    | (Struct_tag _ | Named_tag _ | Anon_tag), _ -> false

  type (+'neg, +'pos) cons_record =
    { tag: tuple_tag option;
      args: ('neg, 'pos) tyarg list;
      body: 'pos Fields.t }

  and (+'neg, +'pos) cons =
    | Top
    | Record of ('neg,'pos) cons_record
    | Func of 'neg list * 'pos

  and (+'neg, +'pos) tyarg =
    | Arg_none
    | Arg_neg of 'neg
    | Arg_pos of 'pos
    | Arg_both of 'neg * 'pos

  let named t =
    Record { tag = Some (Named_tag t); args = []; body = Fields.empty }

  type (+'neg, +'pos) t = ('neg, 'pos) cons

  module Tyarg = struct
    let equal ~neg ~pos a b =
      match a, b with
      | Arg_none, Arg_none -> true
      | Arg_neg a, Arg_neg b -> neg a b
      | Arg_pos a, Arg_pos b -> pos a b
      | Arg_both (na,pa), Arg_both (nb,pb) -> neg na nb && pos pa pb
      | _, _ -> false

    let map ~neg ~pos a =
      match a with
      | Arg_none -> Arg_none
      | Arg_neg a -> Arg_neg (neg a)
      | Arg_pos a -> Arg_pos (pos a)
      | Arg_both (n,p) -> Arg_both (neg n, pos p)

    let iter ~neg ~pos a =
      ignore (map ~neg ~pos a)

    let zip ~neg ~pos a b =
      match a, b with
      | Arg_none, Arg_none -> Arg_none
      | Arg_neg a, Arg_neg b -> Arg_neg (neg a b)
      | Arg_pos a, Arg_pos b -> Arg_pos (pos a b)
      | Arg_both (na,pa), Arg_both (nb,pb) -> Arg_both (neg na nb, pos pa pb)
      | _ -> intfail "Tyarg.zip: mismatched tyargs"

    let proj_neg = function
      | Arg_neg n | Arg_both (n,_) -> n
      | _ -> intfail "Tyarg.proj_neg: variance mismatch"

    let proj_pos = function
      | Arg_pos p | Arg_both (_,p) -> p
      | _ -> intfail "Tyarg.proj_pos: variance mismatch"
  end

  let equal ~neg ~pos p q =
    match p, q with
    | Top, Top -> true
    | Record {tag=ptag; args=pargs; body=pbody},
      Record {tag=qtag; args=qargs; body=qbody} ->
       Option.equal tuple_tag_equal ptag qtag &&
       List.for_all2 (Tyarg.equal ~neg ~pos) pargs qargs &&
       Fields.equal ~pos pbody qbody
    | Func (pa, pr), Func (qa, qr) ->
       List.equal neg pa qa &&
       pos pr qr
    | (Record _|Func _|Top), _ -> false

  let map ~neg ~pos = function
    | Top -> Top
    | Record {tag; args; body} ->
       Record {tag; args = List.map (Tyarg.map ~neg ~pos) args; body = Fields.map ~pos body}
    | Func (args, res) ->
       let args = List.map neg args in
       let res = pos res in
       Func (args, res)

  let wf ~params ~neg ~pos = function
    | Top -> ()
    | Record {tag; args; body} ->
       begin match tag with
       | None | Some (Anon_tag | Struct_tag _) -> assert (args = [])
       | Some (Named_tag (name,_)) ->
          let wf_arg v arg =
            match arg, v.Exp.occurs_neg, v.Exp.occurs_pos with
            | Arg_none, `No, `No
            | Arg_neg _, `Yes, `No
            | Arg_pos _, `No, (`Yes|`Strict)
            | Arg_both _, `Yes, (`Yes|`Strict) -> ()
            | _ -> intfail "wf_arg: tyargs don't match param"
          in
          match params name with
          | pvs ->
             if List.length pvs <> List.length args then
               intfail "Cons.wf: %d args to %s, should be %d" (List.length args) name (List.length pvs)
             List.iter2 wf_arg pvs args;
             List.iter (Tyarg.iter ~neg ~pos) args
          | exception Not_found -> intfail "Cons.wf: %s not in env" name
       end;
       Fields.wf ~pos body
    | Func (args, res) ->
       List.iter neg args;
       pos res

  type field =
    | Func_arg of int
    | Func_res
    | Named_arg of [`Neg|`Pos] * string * int
    | Record_field of Tuple_fields.field_name

  let field_is_positive = function
    | Func_arg _ -> false
    | Named_arg (`Pos,_,_) -> true
    | Named_arg (`Neg,_,_) -> false
    | Func_res | Record_field _ -> true

  let equal_field a b =
    match a, b with
    | Func_arg i, Func_arg j -> i = j
    | Func_res, Func_res -> true
    | Record_field a, Record_field b ->
       Tuple_fields.equal_field_name a b
    | Named_arg (p, s, i), Named_arg (p', s', i') ->
       p = p' && s = s' && i = i'
    | (Func_arg _ | Func_res | Record_field _ | Named_arg _), _ -> false

  let mapi ~neg ~pos = function
    | Top -> Top
    | Record {tag; args; body} ->
       let arg i arg =
         let tag = match tag with
           | Some (Named_tag (t,_)) -> t
           | _ -> intfail "args on invalid type"
         in
         Tyarg.map arg
           ~neg:(fun x -> neg (Named_arg (`Neg, tag, i)) x)
           ~pos:(fun x -> pos (Named_arg (`Pos, tag, i)) x)
       in
       let args = List.mapi arg args in
       let field fn x = pos (Record_field fn) x in
       let body = Fields.mapi ~pos:field body in
       Record {tag; args; body}
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

  type head_ordering =
    | Un of head_conflict
    | Le of head_coercion

  let sub_head p q =
    match p, q with
    | Top, Top -> Le Id
    | _, Top -> Le To_top
    | Top, _ -> Un Incompatible

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
       | Some pt, Some qt when tuple_tag_equal pt qt -> Le Id
       | _, Some qt -> Un (Expected_tag (ptag, [qt]))
       end

  let incomparable_head a b =
    match sub_head a b, sub_head b a with
    | Un _, Un _ -> true
    | _, _ -> false
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
  { dy_lower: (flexvar, lower) Cons1.t loc;
    dy_upper: (lower, flexvar) Cons1.t loc;
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

let compare_typ_var a b =
  match a, b with
  | Vrigid _, Vbound _ -> 1
  | Vbound _, Vrigid _ -> -1
  | Vrigid a, Vrigid b ->
     begin match Env_level.compare a.level b.level with
     | 0 -> compare a.var b.var
     | n -> n
     end
  | Vbound a, Vbound b ->
     begin match compare b.index a.index with
     | 0 -> compare a.var b.var
     | n -> n
     end

let equal_typ_var a b = compare_typ_var a b = 0


type (+'neg, +'pos) typ =
  | Tsimple of 'pos
  | Tcvj of ('neg, 'pos) tcvj
  (* No Tpoly allowed under a join involving vars *)
  | Tpoly of ('neg, 'pos) poly_typ
and (+'neg, +'pos) cons_typ = (('pos, 'neg) typ, ('neg, 'pos) typ) Cons1.t Location.loc
and (+'neg, +'pos) poly_typ =
  { (* names must be distinct *)
    (* bound must be a constructed type, possibly joined with some rigid/bound vars *)
    vars : (string Location.loc * ('pos, 'neg) typ option) iarray;
    body : ('neg, 'pos) typ }

and ('neg,'pos) tcvj =
  ('neg, 'pos) cons_typ list * typ_var list * Location.t option

let tbot loc = Tcvj ([], [], loc)
let ttop loc = Tcvj ([Top, loc], [], Some loc)
let tcons (cons,loc) = Tcvj ([cons,loc], [], Some loc)
let tvar v =
  let loc = match v with Vbound v -> v.loc | Vrigid v -> v.loc in
  Tcvj ([], [v], Some loc)

let is_ttop = function
  | Tcvj([Top, _], _, _) -> true
  | _ -> false

let is_tbot = function
  | Tcvj([], [], _) -> true
  | _ -> false

let is_varjoin : _ tcvj -> bool = function
  | _, [], _ -> false
  | [], [_var], _ -> false
  | _ -> true

let gen_zero : (zero, zero) typ -> ('a, 'b) typ = Obj.magic


type ptyp = (flexvar, lower) typ
type ntyp = (lower, flexvar) typ

type gen_level = env_level option


type decl_fields = (zero,zero) typ Fields.t
type decl_body =
  | Decl_primitive
  | Decl_record of decl_fields
  | Decl_variant of (Exp.symbol * decl_fields) list

let map_decl_body ~pos = function
  | Decl_primitive ->
     Decl_primitive
  | Decl_record fs ->
     Decl_record (Fields.map ~pos fs)
  | Decl_variant vs ->
     Decl_variant (List.map (fun (s,fs) -> s, Fields.map ~pos fs) vs)

type type_decl =
  { name: Exp.symbol;
    params: (Exp.variance_spec * Exp.symbol) list;
    body: decl_body }


type value_binding =
  { typ: ptyp;
    (* The level of the outermost unannotated lambda-bound parameter
       reachable from this binding by expanding untyped let definitions.
       (cf. Haskell's MonoLocalBinds) *)
    gen_level: gen_level;
    comp_var: IR.value IR.Binder.ref
  }

(* Rigid type variables. *)
type rigvar_defn = {
  (* unique among a binding group, but can shadow.
     Only used for parsing/printing: internally, referred to by index. *)
  name : string Location.loc;
  upper : (flexvar, lower) Cons1.t loc list;
}

let n_bool loc = ("Bool", loc)
let n_int loc = ("Int", loc)
let n_string loc = ("String", loc)

module Env = struct
  type bindings =
    | Env_vals of { vals : value_binding SymMap.t; rest : bindings }
    | Env_types of {
        level : env_level;
        rig_names : int SymMap.t;
        rig_defns : rigvar_defn iarray;
        rest : bindings }
    | Env_nil

  type t =
    { env_type_decls: type_decl SymMap.t;
      env_level: env_level;
      env_bindings: bindings }

  let rigid_vars env lvl =
    let rec env_at_level env lvl =
      match env with
      | Env_vals { vals=_; rest } -> env_at_level rest lvl
      | Env_types tys when Env_level.equal tys.level lvl -> env
      | Env_types tys ->
         assert (Env_level.extends lvl tys.level); env_at_level tys.rest lvl
      | Env_nil when Env_level.equal Env_level.initial lvl -> Env_nil
      | Env_nil -> intfail "env level not found"
    in
    match env_at_level env.env_bindings lvl with
    | Env_types tys ->
       assert (Env_level.equal tys.level lvl); tys.rig_defns
    | _ -> intfail "env_rigid_vars"

  let rigid_var env (rv : rigvar) =
    IArray.get (rigid_vars env rv.level) rv.var

  let rigid_bound env rv =
    (rigid_var env rv).upper

  let lookup_value env (v : Exp.ident') =
    let rec search (v : Exp.ident') = function
      | Env_nil -> None
      | Env_vals { vals = vs; rest; _ }
           when SymMap.mem v.label vs ->
         if v.shift = 0 then Some (SymMap.find v.label vs) else
           search { v with shift = v.shift - 1 } rest
      | Env_types { rest; _ } | Env_vals { rest; _ } ->
         search v rest
    in
    search v env.env_bindings

  let lookup_decl env (s : string) =
    SymMap.find_opt s env.env_type_decls

  let level env =
    env.env_level

  let builtins =
    (["Bool", {name = n_bool Location.noloc; params=[]; body=Decl_primitive};
      "Int", {name = n_int Location.noloc; params=[]; body=Decl_primitive};
      "String", {name = n_string Location.noloc; params=[]; body=Decl_primitive}]
     : (string * type_decl) list)
    |> List.to_seq
    |> SymMap.of_seq

  let empty =
    { env_type_decls = builtins;
      env_level = Env_level.initial;
      env_bindings = Env_nil }

  let extend_types env ~level ~rig_names ~rig_defns =
    assert (Env_level.extends env.env_level level);
    assert (not (Env_level.equal env.env_level level));
    let env_bindings = Env_types {level; rig_names; rig_defns; rest=env.env_bindings} in
    { env with env_level = level; env_bindings }

  let extend_types_flex env ~level =
    extend_types env ~level ~rig_names:SymMap.empty ~rig_defns:IArray.empty

  let extend_vals env ~vals =
    { env with env_bindings = Env_vals { vals; rest = env.env_bindings } }

  let extend_decls env decls =
    let env_type_decls =
      List.fold_left (fun acc (d : type_decl) ->
        assert (not (SymMap.mem (fst d.name) acc));
        SymMap.add (fst d.name) d acc)
        env.env_type_decls
        decls
    in
    { env with env_type_decls }

  let param_variances env name =
    (SymMap.find name env.env_type_decls).params |> List.map fst

  let get_decl_fields env (s : string) =
    match lookup_decl env s with
    | None -> intfail "unbound decl %s" s
    | Some {name=_; params=_; body = Decl_primitive } ->
       Fields.empty
    | Some {name=_; params=_; body = Decl_variant _} -> unimp "variant fields"
    | Some {name=_; params=_; body = Decl_record fs} -> fs

  let get_decl_params env (s : string) =
    match lookup_decl env s with
    | None -> intfail "unbound decl %s" s
    | Some decl -> decl.params
end

type env = Env.t

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
    | Urigvar (pv, pds), Urigvar (qv, qds) ->
       equal_rigvar pv qv && List.equal (==) pds qds
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

let rec env_bindings_level (env : Env.bindings) =
  match env with
  | Env_types tys -> tys.level
  | Env_vals vs -> env_bindings_level vs.rest
  | Env_nil -> Env_level.initial

(* visit counters: odd = visiting, even = done *)
let fv_gen_visit_counts env fv =
  let level = Env.level env in
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

let is_locally_closed ix t =
  let var ix = function
    | Vrigid _ -> ()
    | Vbound {index; _} ->
       if index >= ix then raise Exit
  in
  let rec check : 'a 'b . int -> ('a,'b) typ -> unit =
    fun ix ty -> match ty with
    | Tsimple _ -> ()
    | Tcvj (conses, vars, _loc) ->
       List.iter (fun (c,_loc) ->
         ignore (Cons1.map ~neg:(check ix) ~pos:(check ix) c)) conses;
       List.iter (var ix) vars
    | Tpoly {vars; body} ->
       let ix = ix + 1 in
       vars |> IArray.iter (fun (_, b) -> Option.iter (check ix) b);
       check ix body
  in
  match check ix t with
  | () -> true
  | exception Exit -> false

let rec open_typ :
  'neg 'pos .
  neg:(('pos,'neg) tcvj -> int loc list -> ('pos, 'neg) typ) ->
  pos:(('neg,'pos) tcvj -> int loc list -> ('neg, 'pos) typ) ->
  int -> ('neg,'pos) typ -> ('neg,'pos) typ =
  fun ~neg ~pos ix t -> match t with
  | Tsimple _ as s -> s
  | Tcvj (conses, vars, loc) ->
     let conses = List.map (fun (c,cloc) ->
       Cons1.map ~neg:(open_typ ~neg:pos ~pos:neg ix) ~pos:(open_typ ~neg ~pos ix) c, cloc) conses in
     let opened, rest =
       vars |> List.partition_map (function
         | Vbound b when b.index >= ix ->
           assert (b.index = ix);
           Left (b.var, b.loc)
         | v -> Right v)
     in
     begin match opened with
     | [] -> Tcvj (conses, rest, loc)
     | opened -> pos (conses, rest, loc) opened
     end
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, Option.map (open_typ ~neg:pos ~pos:neg ix) b) vars;
            body = open_typ ~neg ~pos ix body}

let rec close_typ :
  'neg 'pos .
  neg:(('pos,'neg) tcvj -> unit) ->
  pos:(('neg,'pos) tcvj -> unit) ->
  Env_level.t -> int -> ('neg, 'pos) typ -> ('neg,'pos) typ =
  fun ~neg ~pos lvl ix t -> match t with
  | Tsimple _ as s -> s
  | Tcvj ((conses, vars, loc) as orig) ->
     let conses =
       conses |> List.map (fun (c, cloc) ->
         (Cons1.map ~neg:(close_typ ~neg:pos ~pos:neg lvl ix) ~pos:(close_typ ~neg ~pos lvl ix) c, cloc))
     in
     let found_close = ref false in
     let vars =
       vars |> List.map (function
         | Vrigid rv when Env_level.extends lvl rv.level ->
            assert (Env_level.equal lvl rv.level);
            found_close := true;
            Vbound {index=ix; var=rv.var; loc=rv.loc}
         | Vrigid _ as v -> v
         | Vbound b as v ->
            assert (b.index < ix);
            v)
     in
     if !found_close then pos orig;
     Tcvj (conses, vars, loc)
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, Option.map (close_typ ~neg:pos ~pos:neg lvl ix) b) vars;
            body = close_typ ~neg ~pos lvl ix body}

let next_flexvar_id = ref 0

let fresh_flexvar' level upper : flexvar =
  let id = !next_flexvar_id in
  incr next_flexvar_id;
  { level; upper; lower = bottom; id; gen = Not_generalising }

let fresh_flexvar level = fresh_flexvar' level Utop

(* FIXME dedup with check_type *)
let rec env_lookup_type_var (env : Env.bindings) loc name : rigvar option =
  match env with
  | Env_vals vs -> env_lookup_type_var vs.rest loc name
  | Env_types ts ->
     begin match SymMap.find name ts.rig_names with
     | var -> Some {level = ts.level; var; loc}
     | exception Not_found -> env_lookup_type_var ts.rest loc name
     end
  | Env_nil -> None

let env_lookup_type_var env loc name = env_lookup_type_var env.Env.env_bindings loc name

let c_bool loc = (Cons1.named (n_bool loc), loc)
let c_int loc = (Cons1.named (n_int loc), loc)
let c_string loc = (Cons1.named (n_string loc), loc)

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
  if not (Env_level.extends fv.level (Env.level env)) then
    intfail "wf_flexvar: %s at %d not inside env %d" (flexvar_name fv) (Env_level.to_int fv.level) (Env_level.to_int (Env.level env));
  assert (Env_level.extends fv.level (Env.level env));
  assert (Env_level.extends fv.level lvl);
  if not (Env_level.equal fv.level Env_level.initial) then
    ignore (Env.rigid_vars env fv.level);
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
  let lvl = dy_flexvar.level in
  Cons1.wf ~params:(Env.param_variances env) ~neg:(wf_flexvar ~seen env lvl) ~pos:(wf_lower ~seen env lvl) (fst dy_lower);
  Cons1.wf ~params:(Env.param_variances env) ~pos:(wf_flexvar ~seen env lvl) ~neg:(wf_lower ~seen env lvl) (fst dy_upper)

and wf_rigvar env lvl (rv : rigvar) =
  assert (Env_level.extends rv.level lvl);
  let rvs = Env.rigid_vars env rv.level in
  assert (0 <= rv.var && rv.var < IArray.length rvs)

and wf_lower_part ~seen env lvl = function
  | Lflexvar v -> wf_flexvar ~seen env lvl v
  | Lrigvar v -> wf_rigvar env lvl v
  | Lcons (c,_) -> Cons1.wf ~params:(Env.param_variances env) ~neg:(wf_flexvar ~seen env lvl) ~pos:(wf_lower ~seen env lvl) c

and wf_lower ~seen env lvl l =
  l |> List.iteri (fun i a ->
    l |> List.iteri (fun j b ->
      if i < j then match a, b with
      | Lflexvar a, Lflexvar b -> assert (not (equal_flexvar a b))
      | Lrigvar a, Lrigvar b -> assert (not (equal_rigvar a b))
      | Lcons (a,_), Lcons (b,_) -> assert (Cons1.incomparable_head a b)
      | _, _ -> ()));
  l |> List.iter (wf_lower_part ~seen env lvl)

let wf_var env ext = function
  | Vrigid rv -> wf_rigvar env rv.level rv
  | Vbound {index; var; loc=_} ->
     assert (0 <= index && index < List.length ext);
     assert (0 <= var && var < snd (List.nth ext index))

let rec wf_typ : 'pos 'neg .
  neg:('neg -> unit) ->
  pos:('pos -> unit) ->
  ispos:bool ->
  env -> int option -> (bool option * int) list -> ('neg, 'pos) typ -> unit =
  fun ~neg ~pos ~ispos env bmin ext ty ->
  match ty with
  | Tsimple s -> pos s
  | Tcvj ((conses, vars, _loc) as cvj) ->
     let posbound =
       vars
       |> List.filter_map (function
         | Vrigid _ -> None
         | Vbound v ->
            assert (v.index < List.length ext);
            bmin |> Option.iter (fun min -> assert (min <= v.index));
            let (bind, count) = List.nth ext v.index in
            assert (v.var < count);
            match bind with
            | None ->
               (* e.g. Elab-bound variable *)
               None
            | Some pol when pol = ispos ->
               (* covariant usage *)
               Some v.index
            | Some _ ->
               (* contravariant usage *)
               assert (not (is_varjoin cvj));
               None)
     in
     let bmin =
       match posbound with
       | [] -> bmin
       | v :: vs ->
          assert (List.for_all (fun v' -> v = v') vs);
          Some v
     in
     conses |> List.iteri (fun i (c, _) ->
       conses |> List.iteri (fun j (d, _) ->
         if i <> j then assert (Cons1.incomparable_head c d)));
     conses |> List.iter (fun (c, _loc) -> Cons1.wf c
       ~params:(Env.param_variances env)
       ~neg:(wf_typ ~neg:pos ~pos:neg ~ispos:(not ispos) env bmin ext)
       ~pos:(wf_typ ~neg ~pos ~ispos env bmin ext))
  | Tpoly {vars; body} ->
     let n_unique_vars = IArray.to_list vars |> List.map fst |> List.map fst |> List.sort_uniq String.compare |> List.length in
     assert (n_unique_vars = IArray.length vars);
     let ext = (Some ispos, IArray.length vars) :: ext in
     let bmin = Option.map ((+) 1) bmin in
     IArray.iter (fun (_, c) ->
       (* FIXME: constraints on c. Can it be e.g. Tsimple?
          Prob not same binder either. *)
       Option.iter (wf_typ ~neg:pos ~pos:neg ~ispos:(not ispos) env bmin ext) c) vars;
     wf_typ ~neg ~pos ~ispos env bmin ext body

let wf_decl env (decl : type_decl) =
  let wf_typ t = wf_typ ~neg:never ~pos:never ~ispos:true env None [None, List.length decl.params] t in
  match decl.body with
  | Decl_primitive -> ()
  | Decl_record fs -> Fields.wf ~pos:wf_typ fs
  | Decl_variant vs ->
     vs |> List.iter (fun (_,fs) -> Fields.wf ~pos:wf_typ fs)

let wf_env env =
  SymMap.iter (fun _ d -> wf_decl env d) env.Env.env_type_decls

(*
 * Unparsing: converting a typ back to a Exp.tyexp
 *)

let mktyexp (t : Exp.tyexp') = (Some t, Location.noloc)

let named_type s : Exp.tyexp' =
  Trecord (Some (Named_tag (s, Location.noloc)), [], Exp.empty_fields)

let mktyvar v = mktyexp (Ttyvar (v, Location.noloc))

let mayloc t = (Some t, Location.noloc)

let unparse_fields ~pos ~tag ({fields; fnames} : _ Fields.t) =
  let open Fields in
  let unparse_field_desc k = function
    | Funknown l -> (k,l), Exp.Optional, None
    | Foptional (a, l) -> (k,l.pres_loc), Exp.Optional, Some (pos a)
    | Fpresent (a, l) -> (k,l), Exp.Mandatory, Some (pos a)
    | Fabsent l -> (k,l), Exp.Optional, Some (mktyexp (Ttyvar ("absent", Location.noloc)))
    | Fbroken l -> (k,l.abs_loc), Exp.Mandatory, Some (mktyexp (Ttyvar ("absent", Location.noloc)))
  in
  match
    if tag = None then raise Exit;
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
     Exp.Ftuple tuple
  | exception Exit ->
     Exp.Frecord (List.map (fun f -> unparse_field_desc f (Map.find f fields)) fnames)

let unparse_cons ~neg ~pos (ty,_tyloc) =
  let open Cons1 in
  let ty = match ty with
    | Top -> named_type "Any"
    | Record {tag; args; body} ->
       let fs = unparse_fields ~pos ~tag body in
       let args =
         (* FIXME: Top/Bot in syntax? *)
         fixme;
         let is_top = function
           | Some (Exp.Trecord (Some (Named_tag ("Any", _)), [], _)), _  -> true
           | _ -> false
         in
         let is_bot = function
           | Some (Exp.Trecord (Some (Named_tag ("Nothing", _)), [], _)), _  -> true
           | _ -> false
         in
         args
         |> List.map (Tyarg.map ~neg ~pos)
         |> List.map (function
           | Arg_none -> Exp.Arg_gen (mayloc (named_type "Any"))
           | Arg_neg t | Arg_pos t -> Exp.Arg_gen t
           | Arg_both (neg, pos) ->
              if Exp.equal_tyexp neg pos
              then Exp.Arg_gen pos
              else if is_bot neg
              then Exp.Arg_pos pos
              else if is_top pos
              then Exp.Arg_neg neg
              else Exp.Arg_both {neg;pos})
       in
       Trecord (tag, List.map mayloc args, fs)
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
  mktyvar name

let unparse_rigid_var ~env:(env,_) rv =
  let name =
    match Env.rigid_var env rv with
    | rv ->
       (* FIXME: this name might be shadowed? *)
       fst rv.name
    | exception _ ->
       Printf.sprintf "##%d.%d" (Env_level.to_int rv.level) rv.var
  in
  mktyvar name

let unparse_flexvar ~env:_ ~flexvar fv =
  flexvar fv;
  let name = flexvar_name fv in
  (* let name = Printf.sprintf "%s@%d" name (Env_level.to_int fv.level) in *)
  mktyvar name

let unparse_var ~env = function
  | Vbound {index; var; loc=_} -> unparse_bound_var ~env index var
  | Vrigid rv -> unparse_rigid_var ~env rv

let unparse_joins = function
  | [] -> mktyexp (named_type "Nothing")
  | [x] -> x
  | x :: xs -> List.fold_left (fun a b -> mktyexp (Exp.Tjoin (a, b))) x xs

let freshen_name (env, ext) name =
  (* FIXME: this sort of freshening or shifts? *)
  (* FIXME: if freshening, use levels somehow to determine when not needed *)
  let taken name =
    env_lookup_type_var env Location.noloc name <> None ||
    List.exists (fun names -> IArray.exists (String.equal name) names) ext in
  let rec freshen name i =
    let p = Printf.sprintf "%s_%d" name i in
    if not (taken p) then p else freshen name (i + 1) in
  if not (taken name) then name else freshen name 2

let rec unparse_gen_typ :
  'neg 'pos . env:(_ * _) -> neg:(env:(env*_) -> 'neg -> Exp.tyexp) -> pos:(env:(env*_) -> 'pos -> Exp.tyexp) ->
             ('neg,'pos) typ -> Exp.tyexp =
  fun ~env ~neg ~pos ty -> match ty with
  | Tsimple t -> pos ~env t
  | Tcvj (conses, vars, _loc) ->
     let joinands =
       List.map (unparse_cons ~neg:(unparse_gen_typ ~env ~neg:pos ~pos:neg) ~pos:(unparse_gen_typ ~env ~neg ~pos)) conses
       @ List.map (unparse_var ~env) vars
     in
     begin match joinands with
     | [] -> mktyexp (named_type "Nothing")
     | j :: js ->
        let tjoin a b = mktyexp (Exp.Tjoin (a, b)) in
        List.fold_left tjoin j js
     end
  | Tpoly { vars; body } ->
     let env, bounds = unparse_bounds ~bound:(unparse_gen_typ ~neg:pos ~pos:neg) ~env vars in
     mktyexp (Exp.Tforall(bounds, unparse_gen_typ ~env ~neg ~pos body))

and unparse_bounds :
  'b . env:_ -> bound:(env:(env*_) -> 'b -> Exp.tyexp) ->
             (string Location.loc * 'b option) iarray -> _ * Exp.typolybounds =
  fun ~env:(env,ext) ~bound vars ->
  let vars = IArray.map (fun ((s,l), b) -> (freshen_name (env,ext) s,l), b) vars in
  let ext = IArray.map (fun ((s,_),_) -> s) vars :: ext in
  (env,ext), IArray.map (fun ((s,_), boundopt) ->
       let s = (s, Location.noloc) in
       match boundopt with
       | None -> s, None
       | Some t ->
          s, Some (bound ~env:(env,ext) t)) vars |> IArray.to_list

let unparse_join = function
  | [] -> mktyexp (named_type "Nothing")
  | t :: ts ->
     List.fold_left (fun a b -> mktyexp (Exp.Tjoin (a, b))) t ts

let rec unparse_lower_part ~env ~flexvar = function
  | Lflexvar fv -> unparse_flexvar ~env ~flexvar fv
  | Lrigvar rv -> unparse_rigid_var ~env rv
  | Lcons c -> unparse_cons c ~neg:(unparse_flexvar ~env ~flexvar) ~pos:(unparse_lower ~env ~flexvar)

and unparse_lower ~env ~flexvar l =
  l
  |> List.map (unparse_lower_part ~env ~flexvar)
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

let unparse_ptyp ~flexvar ?(env=(Env.empty,[])) (t : ptyp) =
  unparse_gen_typ ~env ~neg:(unparse_flexvar ~flexvar) ~pos:(unparse_lower ~flexvar) t
let unparse_ntyp ~flexvar ?(env=(Env.empty,[])) (t : ntyp) =
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
  let doc = unparse_lower ~env:(Env.empty,[]) ~flexvar:ignore t in
  pp_tyexp ppf doc

let pp_upper ~flexvar ~env ppf t =
  let env = env, [] in
  let tys = unparse_upper ~env ~flexvar t in
  let docs = List.map Print.tyexp tys in
  pp_doc ppf (PPrint.(separate (comma ^^ space) docs))

let pp_flexvar ppf v =
  let env = Env.empty, [] in
  pp_tyexp ppf (unparse_flexvar ~env ~flexvar:ignore v)

let pp_ntyp ppf t =
  let env = Env.empty, [] in
  pp_tyexp ppf (unparse_ntyp ~env ~flexvar:ignore t)

let pp_ptyp ppf t =
  let env = Env.empty, [] in
  pp_tyexp ppf (unparse_ptyp ~env ~flexvar:ignore t)

let fmt_unit_typ ~env t =
  unparse_gen_typ t
    ~env
    ~neg:(fun ~env:_ () -> (mktyexp (named_type "_")))
      ~pos:(fun ~env:_ () -> (mktyexp (named_type "_")))
  |> Print.tyexp

let pp_unit_typ ~env ppf t =
  pp_doc ppf (fmt_unit_typ ~env t)

let with_dump_fv ~env ppf f =
  let env = env, [] in
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
  in
  f ~flexvar;
  let fvs = !fv_list |> List.rev |> List.map (fun i -> let (n, t) = (Hashtbl.find fvs i) in n, Option.get t) in
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
       Format.fprintf ppf "\n");
  Format.fprintf ppf "%!"


let dump_ptyp ppf t =
  let env = Env.empty, [] in
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


let wf_ptyp ?(ext=[]) env (t : ptyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~neg:(wf_flexvar ~seen env (Env.level env)) ~pos:(wf_lower ~seen env (Env.level env)) ~ispos:true env None ext t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ptyp t

let wf_ntyp ?(ext=[]) env (t : ntyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~neg:(wf_lower ~seen env (Env.level env)) ~pos:(wf_flexvar ~seen env (Env.level env)) ~ispos:false env None ext t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ntyp t
