(*
 * Core definitions used by the typechecker
 *)

module StrMap = Map.Make (struct type t = string let compare = compare end)

exception Internal of string
let intfail fmt =
  Format.kasprintf (fun s -> raise (Internal s)) fmt
let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

exception Unimplemented of string
let unimp fmt =
  Format.kasprintf (fun s -> raise (Unimplemented s)) fmt
let () = Printexc.register_printer (function Unimplemented s -> Some ("unimplemented: " ^ s) | _ -> None)

let id x = x

type zero = |
let never : zero -> 'a = function _ -> .


(* FIXME move *)
module Ivar : sig
  type 'a put
  type 'a get
  val make : unit -> 'a put * 'a get
  val put : 'a put -> 'a -> unit
  val get : 'a get -> 'a
end = struct
  type 'a put = 'a option ref
  type 'a get = 'a option ref
  let make () = let r = ref None in r,r
  let put r x =
    assert (!r = None);
    r := Some x
  let get r =
    Option.get !r
end

(* Immutable arrays *)
module IArray : sig
  type +'a t
  val empty : 'a t
  val make : 'a array -> 'a t
  val get : 'a t -> int -> 'a
  val length : 'a t -> int
  val of_list : 'a list -> 'a t
  val of_array : 'a array -> 'a t
  val to_list : 'a t -> 'a list
  val to_array : 'a t -> 'a array
  val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val iter : ('a -> unit) -> 'a t -> unit
  val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val exists : ('a -> bool) -> 'a t -> bool
  val map_fold_left : ('s -> 'a -> 's * 'b) -> 's -> 'a t -> 's * 'b t
end = struct
  type +'a t = Mk : 'b array * ('b -> 'a) -> 'a t
  let acopy a = Array.map id a
  let empty = Mk ([| |], id)
  let make x = Mk (Array.map id x, id)
  let get (Mk (a, r)) i = r a.(i)
  let length (Mk (a, _r)) = Array.length a
  let of_list l = make (Array.of_list l)
  let of_array a = Mk(acopy a, id)
  let to_array (Mk (a, r)) = Array.map r a
  let to_list x = to_array x |> Array.to_list
  let map f (Mk (a, r)) = Mk (Array.init (Array.length a) (fun i -> f (r a.(i))), id)
  let mapi f (Mk (a, r)) = Mk (Array.init (Array.length a) (fun i -> f i (r a.(i))), id)
  let iter2 f (Mk (a, ra)) (Mk (b, rb)) =
    Array.iter2 (fun a b -> f (ra a) (rb b)) a b
  let iter f (Mk (a, r)) = Array.iter (fun x -> f (r x)) a
  let exists f (Mk (a, r)) = Array.exists (fun x -> f (r x)) a
  let map_fold_left f s (Mk (a, r)) =
    let st = ref s in
    let out = ref [| |] in
    for i = 0 to Array.length a - 1 do
      let x = a.(i) in
      let s, b = f !st (r x) in
      let out =
        match !out with
        | [| |] -> out := Array.make (Array.length a) b; !out
        | o -> o in
      out.(i) <- b;
      st := s
    done;
    !st, of_array !out
end
type 'a iarray = 'a IArray.t

open Tuple_fields

(* Head type constructors. These do not bind type variables. *)
type (+'neg, +'pos) cons_head =
  | Top
  | Bot
  (* FIXME: maybe delete these once abstypes exist? *)
  | Bool
  | Int
  | String
  | Record of 'pos tuple_fields
  | Func of 'neg tuple_fields * 'pos

let map_head neg pos = function
  | Top -> Top
  | Bot -> Bot
  | Bool -> Bool
  | Int -> Int
  | String -> String
  | Record fields -> Record (map_fields (fun _fn x -> pos x) fields)
  | Func (args, res) ->
     Func (map_fields (fun _fn x -> neg x) args, pos res)

let equal_cons neg pos p q =
  match p, q with
  | Top, Top -> true
  | Bot, Bot -> true
  | Bool, Bool -> true
  | Int, Int -> true
  | String, String -> true
  | Record p, Record q ->
     equal_fields pos p q
  | Func (pa, pr), Func (qa, qr) ->
     equal_fields neg pa qa && pos pr qr
  | (Top|Bot|Bool|Int|String|Record _|Func _), _ -> false

module Env_level : sig
  type t

  val initial : t

  val extend : t -> t
  val replace : t -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val extends : t -> t -> bool

  val to_int : t -> int
end = struct
  (* Not actually mutable, but marking it as such
     makes physical equality work *)
  type t =
    { mutable level : int }

  let initial = { level = 0 }
  let extend { level } = { level = level + 1 }
  let replace { level } = { level }

  let compare { level=l1} {level=l2} = compare l1 l2

  let extends {level=l1} {level=l2} = l1 <= l2

  let equal l1 l2 =
    if l1.level = l2.level then
      (assert (l1 == l2); true)
    else
      false

  let to_int l = l.level
end

type env_level = Env_level.t

(* Rigid variables are immutable.
   Their bounds are stored in the environment. *)
type rigvar =
  { level: env_level;
    var: int }

(* A ctor_ty is a join of a constructed type and some rigid variables *)
type (+'neg,+'pos) ctor_ty =
  { cons: ('neg,'pos) cons_head; rigvars: rigvar list }

(* FIXME: most uses of this function are probably bugs: rigvars need attention *)
let map_ctor_rig neg pos { cons; rigvars } = { cons = map_head neg pos cons; rigvars }



(* Flexvars are mutable but only in one direction.
     - level may decrease
     - bounds may become tighter (upper decreases, lower increases) *)
type flexvar =
  { mutable level: env_level;
    mutable upper: styp_neg; (* strictly covariant parts are matchable *)
    mutable lower: flex_lower_bound; (* If lower is nontrivial, then upper must be UBcons. FIXME: encode this? *)
    (* used for printing *)
    id: int;
    (* used during generalisation *)
    mutable pos_visit_count : int;
    mutable neg_visit_count : int;
    mutable bound_var : int; }

(* A well-formed negative styp is either:
     - a single flexible variable
     - a constructed type, possibly joined with some rigid variables
   Here, the type parameter 'a determines the makeup of constructed types *)
and styp_neg =
    (* f.upper = UBnone: no upper bound *)
  | UBnone
    (* f.upper = UBvar v: *only* upper bound is v. *)
  | UBvar of flexvar
    (* arbitrary upper bounds.
       Only one allowed per set of rigid variables *)
  | UBcons of (flex_lower_bound, flexvar) ctor_ty list

(* Matchability constraint: the contravariant parts of a flexible variable's lower bound must be flexible variables.
   Flexible variables appearing in vars must not have UBvar upper bounds, as they are also constrained above here.
   Flexible variables appearing negatively in ctor might well have UBvar upper bounds.
 *)
and flex_lower_bound =
  { ctor: (flexvar, flex_lower_bound) ctor_ty; flexvars: flexvar list }

type typ_var =
  | Vbound of {index: int; var:int}
  | Vflex of flexvar
  | Vrigid of rigvar

type (+'neg, +'pos) typ =
  | Tsimple of 'pos
  | Tcons of ('neg, 'pos) cons_typ
  | Tvar of typ_var
  | Tvjoin of ('neg, 'pos) typ * typ_var
     (* Tvjoin(t,v): t must be well-scoped at level of var *)
  | Tpoly of {
     (* names must be distinct *)
     (* bound must be a constructed type, possibly joined with some rigid/bound vars *)
     vars : (string * ('pos, 'neg) typ) iarray;
     body : ('neg, 'pos) typ }
and (+'neg, +'pos) cons_typ = (('pos, 'neg) typ, ('neg, 'pos) typ) cons_head

type ptyp = (flexvar, flex_lower_bound) typ
type ntyp = (flex_lower_bound, flexvar) typ

type env =
  | Env_vals of { vals : ptyp SymMap.t; rest : env }
  | Env_types of { level : env_level; rig_names : int SymMap.t; rig_defns : rigvar_defn iarray; rest : env }
  | Env_nil

(* Rigid type variables. *)
and rigvar_defn = {
  (* unique among a binding group, but can shadow.
     Only used for parsing/printing: internally, referred to by index. *)
  name : string;
  (* FIXME: ctor_ty? Are rigid vars allowed in upper bound heads?
     FIXME: this seems very dubious *)
  upper : (flexvar, flex_lower_bound) ctor_ty;
}

(*
 * Equality checks (Syntactic, not subtyping-aware)
 *)

let equal_flexvar (p : flexvar) (q : flexvar) =
  p == q
let equal_rigvar (p : rigvar) (q : rigvar) =
  Env_level.equal p.level q.level && p.var = q.var
let compare_rigvar (p : rigvar) (q : rigvar) =
  let cmp = compare (Env_level.to_int p.level) (Env_level.to_int q.level) in
  if cmp <> 0 then cmp else
    (assert (Env_level.equal p.level q.level); compare p.var q.var)
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
let rec equal_flex_lower_bound (p : flex_lower_bound) (q : flex_lower_bound) =
  equal_lists equal_flexvar p.flexvars q.flexvars &&
  equal_lists equal_rigvar p.ctor.rigvars q.ctor.rigvars &&
  equal_cons equal_flexvar equal_flex_lower_bound p.ctor.cons q.ctor.cons
let equal_styp_neg (p : styp_neg) (q : styp_neg) =
  match p, q with
  | UBnone, UBnone -> true
  | UBvar pv, UBvar qv -> equal_flexvar pv qv
  | UBcons cps, UBcons cqs ->
     equal_lists (fun cp cq ->
       equal_lists equal_rigvar cp.rigvars cq.rigvars &&
       equal_cons equal_flex_lower_bound equal_flexvar cp.cons cq.cons) cps cqs
  | (UBnone|UBvar _|UBcons _), _ -> false

(*
 * Flexvar mutations and backtracking log
 *)

type flexvar_change =
  | Change_level of flexvar * env_level
  | Change_upper of flexvar * styp_neg
  | Change_lower of flexvar * flex_lower_bound

let fv_set_level ~changes fv level =
  changes := Change_level (fv, fv.level) :: !changes;
  fv.level <- level

let fv_set_upper ~changes fv upper =
  changes := Change_upper (fv, fv.upper) :: !changes;
  fv.upper <- upper

let fv_set_lower ~changes fv lower =
  List.iter (fun fv' -> assert (fv != fv')) lower.flexvars;
  changes := Change_lower (fv, fv.lower) :: !changes;
  fv.lower <- lower

let fv_maybe_set_lower ~changes fv lower =
  if not (equal_flex_lower_bound fv.lower lower) then
    (fv_set_lower ~changes fv lower; true)
  else false

let fv_maybe_set_upper ~changes (fv : flexvar) upper =
  if not (equal_styp_neg fv.upper upper) then
    (fv_set_upper ~changes fv upper; true)
  else false

let revert changes =
  changes |> List.iter (function
  | Change_level (fv, level) -> fv.level <- level
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

let env_rigid_bound env (rv : rigvar) =
  (IArray.get (env_rigid_vars env rv.level) rv.var).upper

let rec env_level env =
  match env with
  | Env_types tys -> tys.level
  | Env_vals vs -> env_level vs.rest
  | Env_nil -> Env_level.initial

(*
 * Opening/closing of binders
 *)


let map_head_cons pol f fields =
  map_fields (fun _fn x -> f pol x) fields

let open_typ_var f ix = function
  | Vbound {index; var} when index >= ix ->
     assert (index = ix); f var
  | v -> v

let rec open_typ :
  'neg 'pos . (int -> typ_var) -> int -> ('neg, 'pos) typ -> ('neg, 'pos) typ =
  fun var ix t -> match t with
  | Tsimple _ as s -> s
  | Tcons c -> Tcons (map_head (open_typ var ix) (open_typ var ix) c)
  | Tvar v -> Tvar (open_typ_var var ix v)
  | Tvjoin (t, v) -> Tvjoin(open_typ var ix t, open_typ_var var ix v)
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, open_typ var ix b) vars;
            body = open_typ var ix body}

let open_typ_rigid vars t =
  open_typ (fun i -> Vrigid (IArray.get vars i)) 0 t
let open_typ_flex vars t =
  open_typ (fun i -> Vflex (IArray.get vars i)) 0 t


let close_typ_var lvl f ~ispos ~isjoin index = function
  | Vrigid {level; _} as v when Env_level.equal lvl level ->
     Vbound {index; var = f v ~ispos ~isjoin}
  | Vflex fv as v when Env_level.equal lvl fv.level ->
     Vbound {index; var = f v ~ispos ~isjoin}
  | v -> v

(* Can only be used on typs without Tsimple nodes.
   (This limits it to use during parsing, which does not generate Tsimple) *)
let rec close_typ :
  'a 'b . env_level -> (typ_var -> ispos:bool -> isjoin:bool -> int) -> ispos:bool -> int -> (zero, zero) typ -> ('a, 'b) typ
  = fun lvl var ~ispos ix ty -> match ty with
  | Tsimple z -> never z
  | Tcons c -> Tcons (map_head (close_typ lvl var ~ispos:(not ispos) ix) (close_typ lvl var ~ispos ix) c)
  | Tvar v -> Tvar (close_typ_var lvl var ~ispos ~isjoin:false ix v)
  | Tvjoin (t, v) -> 
     Tvjoin(close_typ lvl var ~ispos ix t,
            close_typ_var lvl var ~ispos ~isjoin:true ix v)
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, close_typ lvl var ~ispos:(not ispos) ix b) vars;
            body = close_typ lvl var ~ispos ix body}

let close_typ_rigid ~ispos level ty =
  let close_var v ~ispos ~isjoin =
    (* FIXME report this better *)
    if isjoin && not ispos then failwith "contravariant join";
    match v with
    | Vrigid v when Env_level.equal v.level level -> v.var
    | _ -> intfail "close_typ_rigid: not a rigid variable" in
  close_typ level close_var ~ispos 0 ty


let next_flexvar_id = ref 0
let fresh_flexvar_gen level upper : flexvar =
  let id = !next_flexvar_id in
  incr next_flexvar_id;
  { level; upper; lower = { ctor = { cons = Bot; rigvars = [] } ; flexvars = [] }; id;
    pos_visit_count = 0; neg_visit_count = 0; bound_var = -1 }


(*
FIXME: this is needed for parsing. Even flexible variables can be looked up!

let rec env_lookup_type_var env name : (styp * styp) option =
  match env with
  | Env_cons { level; entry = (Erigid { names; _ } | Eflexible { names; _ }); _ }
       when SymMap.mem name names ->
     (* FIXME shifting? *)
     let i = SymMap.find name names in
     Some (styp_var Neg level i,
           styp_var Pos level i)
  | Env_cons { rest; _ } -> env_lookup_type_var rest name
  | Env_nil -> None
*)

 
let rec env_lookup_type_var env name : rigvar option =
  match env with
  | Env_vals vs -> env_lookup_type_var vs.rest name
  | Env_types ts ->
     begin match SymMap.find name ts.rig_names with
     | var -> Some {level = ts.level; var}
     | exception Not_found -> env_lookup_type_var ts.rest name
     end
  | Env_nil -> None

let lookup_named_type = function
  | "any" -> Some Top
  | "nothing" -> Some Bot
  | "bool" -> Some Bool
  | "int" -> Some Int
  | "string" -> Some String
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
  List.iter (fun fv' -> assert (fv != fv')) fv.lower.flexvars;
  wf_flex_lower_bound ~seen env fv.level fv.lower;
  match fv.upper with
  | UBnone -> assert (fv.lower = {ctor={cons=Bot;rigvars=[]};flexvars=[]})
  | UBvar v ->
     assert (fv.lower = {ctor={cons=Bot;rigvars=[]};flexvars=[]});
     (* FIXME: same level? *)
     wf_flexvar ~seen env fv.level v
  | UBcons cns ->
     (* Rigvar sets must be distinct *)
     let rvsets = List.map (fun rv -> rv.rigvars) cns in
     let rvsets_uniq = List.sort_uniq (compare_lists compare_rigvar) rvsets in
     assert (List.length rvsets = List.length rvsets_uniq);
     (* Each rigvar set must contain all of the rigvars in the lower bound *)
     let rvlow = fv.lower.ctor.rigvars in
     cns |> List.iter (fun {cons=_;rigvars} ->
       rvlow |> List.iter (fun rv -> assert (List.exists (equal_rigvar rv) rigvars)));
     (* Well-formedness of bounds *)
     cns |> List.iter (fun {cons;rigvars} ->
       assert (rigvars = List.sort_uniq compare_rigvar rigvars);
       map_head (wf_flex_lower_bound ~seen env fv.level) (wf_flexvar ~seen env fv.level) cons |> ignore)
  end

and wf_rigvar env lvl (rv : rigvar) =
  assert (Env_level.extends rv.level lvl);
  let rvs = env_rigid_vars env rv.level in
  assert (0 <= rv.var && rv.var < IArray.length rvs)

and wf_flex_lower_bound ~seen env lvl ({ctor={cons;rigvars}; flexvars} : flex_lower_bound) =
  (* FIXME check for duplicate vars? (Not really a problem, but annoying) *)
  List.iter (wf_flexvar ~seen env lvl) flexvars;
  List.iter (wf_rigvar env lvl) rigvars;
  map_head (wf_flexvar ~seen env lvl) (wf_flex_lower_bound ~seen env lvl) cons |> ignore



let wf_var ~seen env ext = function
  | Vflex fv -> wf_flexvar ~seen env fv.level fv
  | Vrigid rv -> wf_rigvar env rv.level rv
  | Vbound {index; var} ->
     assert (0 <= index && index < List.length ext);
     assert (0 <= var && var < snd (List.nth ext index))

let rec wf_typ : 'pos 'neg .
  seen:_ ->
  neg:('neg -> unit) ->
  pos:('pos -> unit) ->
  ispos:bool -> env -> (bool * int) list -> ('neg, 'pos) typ -> unit =
  fun ~seen ~neg ~pos ~ispos env ext ty ->
  match ty with
  | Tsimple s -> pos s
  | Tcons c ->
     map_head (wf_typ ~seen ~neg:pos ~pos:neg ~ispos:(not ispos) env ext) (wf_typ ~seen ~neg ~pos ~ispos env ext) c |> ignore
  | Tvar v -> wf_var ~seen env ext v
  | Tvjoin (t, v) ->
     wf_var ~seen env ext v;
     begin match v with
     | Vbound v ->
        assert (fst (List.nth ext v.index) = ispos); (* covariant *)
        (* Tvjoin restriction: in T | b, where b is a bound var, T must not mention deeper bindings *)
        let ext = List.mapi (fun ix (pol, len) -> if ix < v.index then (pol, 0) else (pol, len)) ext in
        wf_typ ~seen ~neg ~pos ~ispos env ext t
     | Vflex _ ->
        assert ispos; (* positive *)
        wf_typ ~seen ~neg ~pos ~ispos env [] t
     | Vrigid _ ->
        wf_typ ~seen ~neg ~pos ~ispos env [] t
     end
  | Tpoly {vars; body} ->
     let n_unique_vars = IArray.to_list vars |> List.map fst |> List.sort_uniq String.compare |> List.length in
     assert (n_unique_vars = IArray.length vars);
     let ext = (ispos, IArray.length vars) :: ext in
     IArray.iter (fun (_, c) ->
       (* FIXME: constraints on c. Can it be e.g. Tsimple?
          Not Vflex, at least. Prob not same binder either. *)
       wf_typ ~seen ~neg:pos ~pos:neg ~ispos:(not ispos) env ext c) vars;
     wf_typ ~seen ~neg ~pos ~ispos env ext body



(*
 * Unparsing: converting a typ back to a Exp.tyexp
 *)

let loc : Exp.location =
 { source = "<none>";
   loc_start = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0};
   loc_end = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0} }

let mktyexp t = (Some t, loc)

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, loc)

let unparse_cons ~neg ~pos ty =
  let ty = match ty with
    | Top -> named_type "any"
    | Bot -> named_type "nothing"
    | Bool -> named_type "bool"
    | Int -> named_type "int"
    | String -> named_type "string"
    | Record fs ->
       Trecord (Tuple_fields.map_fields (fun _ t -> pos t) fs)
    | Func (args, ret) ->
       Tfunc (Tuple_fields.map_fields (fun _ t -> neg t) args,
              pos ret) in
  mktyexp ty

let unparse_bound_var ~ext index var =
  let name =
    if index < List.length ext then
      IArray.get (List.nth ext index) var
    else
      match index - List.length ext with
      | 0 -> Printf.sprintf "$%d" var
      | n -> Printf.sprintf "$%d.%d" n var in
  mktyexp (named_type name)


let unparse_rigid_var {level;var} =
  mktyexp (named_type (Printf.sprintf "%d.%d" (Env_level.to_int level) var))

let unparse_flexvar ~flexvar fv =
  flexvar fv;
  let name = flexvar_name fv in
  let name = 
    if fv.pos_visit_count <> 0 || fv.neg_visit_count <> 0 then
      (*Format.sprintf "%s[-%d+%d]" name fv.neg_visit_count fv.pos_visit_count*)
      name
    else
      name (*Format.sprintf "%s@%d" name (Env_level.to_int fv.level)*)
 in
  mktyexp (named_type name)

let unparse_var ~flexvar ~ext = function
  | Vbound {index; var} -> unparse_bound_var ~ext index var
  | Vflex fv -> unparse_flexvar ~flexvar fv
  | Vrigid rv -> unparse_rigid_var rv

let unparse_join ty rigvars =
  List.fold_left (fun c r -> mktyexp (Exp.Tjoin (c, unparse_rigid_var r))) ty rigvars

let rec unparse_gen_typ :
  'neg 'pos . flexvar:_ -> ext:_ -> neg:('neg -> Exp.tyexp) -> pos:('pos -> Exp.tyexp) ->
             ('neg,'pos) typ -> Exp.tyexp =
  fun ~flexvar ~ext ~neg ~pos ty -> match ty with
  | Tsimple t -> pos t
  | Tcons c -> unparse_cons ~neg:(unparse_gen_typ ~flexvar ~ext ~neg:pos ~pos:neg) ~pos:(unparse_gen_typ ~flexvar ~ext ~neg ~pos) c
  | Tvar var
  | Tvjoin (Tcons Bot, var) ->
     unparse_var ~flexvar ~ext var
  | Tvjoin (rest, var) ->
     mktyexp (Exp.Tjoin (unparse_gen_typ ~flexvar ~ext ~neg ~pos rest, unparse_var ~flexvar ~ext var))
  | Tpoly { vars; body } ->
     let ext, bounds = unparse_bounds ~flexvar ~ext ~neg ~pos vars in
     mktyexp (Exp.Tforall(bounds, unparse_gen_typ ~flexvar ~ext ~neg ~pos body))

and unparse_bounds :
  'neg 'pos . flexvar:_ -> ext:_ -> neg:('neg -> Exp.tyexp) -> pos:('pos -> Exp.tyexp) ->
             (string * ('pos,'neg) typ) iarray -> _ * Exp.typolybounds =
  fun ~flexvar ~ext ~neg ~pos vars ->
  (* FIXME: this sort of freshening or shifts? *)
  (* FIXME: if freshening, use levels somehow to determine when not needed *)
  let taken name =
    lookup_named_type name <> None || List.exists (fun names -> IArray.exists (String.equal name) names) ext in
  let rec freshen name i =
    let p = Printf.sprintf "%s_%d" name i in
    if not (taken p) then p else freshen name (i + 1) in
  let freshen name =
    if not (taken name) then name else freshen name 2 in
  let vars = IArray.map (fun (s, b) -> freshen s, b) vars in
  let ext = IArray.map fst vars :: ext in
  ext, IArray.map (fun (s, bound) ->
       let s = (s, loc) in
       match bound with
       | Tcons Top ->
          s, None
       | t ->
          s, Some (unparse_gen_typ ~flexvar ~ext ~pos:neg ~neg:pos t)) vars |> IArray.to_list

let rec unparse_flex_lower_bound ~flexvar { ctor; flexvars } =
  let t =
    match ctor with
    | { cons = Bot; rigvars = [] } -> None
    | { cons; rigvars } ->
       let cons = unparse_cons ~neg:(unparse_flexvar ~flexvar) ~pos:(unparse_flex_lower_bound ~flexvar) cons in
       Some (unparse_join cons rigvars) in
  let tjoin a b =
    match a with
    | None -> Some b
    | Some a -> Some (mktyexp (Exp.Tjoin (a, b))) in
  match
    List.fold_left (fun t fv -> tjoin t (unparse_flexvar ~flexvar fv)) t flexvars
  with
  | Some t -> t
  | None -> unparse_cons ~neg:never ~pos:never Bot

let unparse_ptyp ~flexvar ?(ext=[]) (t : ptyp) =
  unparse_gen_typ ~flexvar ~ext ~neg:(unparse_flexvar ~flexvar) ~pos:(unparse_flex_lower_bound ~flexvar) t
let unparse_ntyp ~flexvar ?(ext=[]) (t : ntyp) =
  unparse_gen_typ ~flexvar ~ext ~neg:(unparse_flex_lower_bound ~flexvar) ~pos:(unparse_flexvar ~flexvar) t



(* For debugging *)
let pp_tyexp ppf ty =
  let buf = Buffer.create 100 in
  let ty = Exp.map_tyexp Exp.normalise ty in
  PPrint.ToBuffer.pretty 1. 10000 buf (PPrint.group (Print.tyexp ty));
  Format.fprintf ppf "%s" (Buffer.to_bytes buf |> Bytes.to_string)

let pp_cons_pos ppf t =
  let cons = unparse_cons ~neg:(unparse_flexvar ~flexvar:ignore) ~pos:(unparse_flex_lower_bound ~flexvar:ignore) t.cons in
  let doc = unparse_join cons t.rigvars in
  pp_tyexp ppf doc

let pp_cons_neg ppf t =
  let cons = unparse_cons ~neg:(unparse_flex_lower_bound ~flexvar:ignore) ~pos:(unparse_flexvar ~flexvar:ignore)  t.cons in
  let doc = unparse_join cons t.rigvars in
  pp_tyexp ppf doc

let pp_flexlb ppf t =
  let doc = unparse_flex_lower_bound ~flexvar:ignore t in
  pp_tyexp ppf doc

let pp_flexvar ppf v =
  pp_tyexp ppf (unparse_flexvar ~flexvar:ignore v)

let pp_ntyp ppf t =
  pp_tyexp ppf (unparse_ntyp ~flexvar:ignore t)

let pp_ptyp ppf t =
  pp_tyexp ppf (unparse_ptyp ~flexvar:ignore t)

let dump_ptyp ppf t =
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
         match fv.lower with
         | {ctor={cons=Bot; rigvars=[]}; flexvars=[]} -> None
         | l -> Some (unparse_flex_lower_bound ~flexvar l) in
       let u =
         match fv.upper with
         | UBvar v -> [unparse_flexvar ~flexvar v]
         | UBnone -> []
         | UBcons cns ->
            cns |> List.map (fun {cons;rigvars} ->
            let cons = unparse_cons ~neg:(unparse_flex_lower_bound ~flexvar) ~pos:(unparse_flexvar ~flexvar) cons in
            unparse_join cons rigvars) in
       Hashtbl.replace fvs fv.id (fv_name, Some (l, u));
       ()
  and unparse t =
    unparse_ptyp ~flexvar t
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


let wf_ptyp env (t : ptyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~seen ~neg:(wf_flexvar ~seen env (env_level env)) ~pos:(wf_flex_lower_bound ~seen env (env_level env)) ~ispos:true env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ptyp t

let wf_ntyp env (t : ntyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~seen ~neg:(wf_flex_lower_bound ~seen env (env_level env)) ~pos:(wf_flexvar ~seen env (env_level env)) ~ispos:false env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ntyp t
