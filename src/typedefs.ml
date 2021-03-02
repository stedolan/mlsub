(*
 * Core definitions used by the typechecker
 *)

module StrMap = Map.Make (struct type t = string let compare = compare end)

exception Internal of string
let intfail fmt =
  Printf.ksprintf (fun s -> raise (Internal s)) fmt
let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

exception Unimplemented of string
let unimp fmt =
  Printf.ksprintf (fun s -> raise (Unimplemented s)) fmt
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


module Env_level : sig
  type t

  val initial : t

  val extend : t -> t
  val replace : t -> t

  val equal : t -> t -> bool
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
    (* arbitrary upper bound *)
  | UBcons of (flex_lower_bound, flexvar) ctor_ty

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
  (* FIXME: ctor_ty? Are rigid vars allowed in upper bound heads? *)
  upper : (flexvar, flex_lower_bound) ctor_ty;
}


(*
 * Environment ordering
 *)
(*
let rec env_at_level' env lvl =
  match env with
  | Env_nil -> failwith "malformed env: level not found"
  | Env_cons { level; entry; _ } when Env_level.equal lvl level ->
     env, entry
  | Env_cons { level; rest; _ } ->
     assert (Env_level.extends lvl level);
     env_at_level' rest lvl

let env_at_level env lvl = fst (env_at_level' env lvl)

let env_entry_at_level env lvl = snd (env_at_level' env lvl)

(* Check that one environment is an extension of another *)
let assert_env_prefix env ext =
  match ext with
  | Env_nil -> assert (env = Env_nil)
  | Env_cons { level; _ } ->
     ignore (env_entry_at_level env level)


let env_next_level env =
  match env with
  | Env_nil -> Env_level.initial ()
  | Env_cons { level; _ } -> Env_level.extend level

let env_cons rest level entry =
  Env_cons { level; entry; rest }

let env_cons_entry rest entry =
  Env_cons { level = env_next_level rest;
             entry;
             rest }

let env_replace env level newlevel entry =
  assert (Env_level.to_int level = Env_level.to_int newlevel);
  match env with
  | Env_cons {level=l; entry=_; rest} when Env_level.equal level l ->
     Env_cons {level=newlevel; entry; rest}
  | _ -> assert false
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


let close_typ_var lvl f index = function
  | Vrigid {level; _} as v when Env_level.equal lvl level ->
     Vbound {index; var = f v}
  | Vflex fv as v when Env_level.equal lvl fv.level ->
     Vbound {index; var = f v}
  | v -> v

(* Can only be used on typs without Tsimple nodes.
   (This limits it to use during parsing, which does not generate Tsimple) *)
let rec close_typ : 
  'a 'b . env_level -> (typ_var -> int) -> int -> (zero, zero) typ -> ('a, 'b) typ
  = fun lvl var ix ty -> match ty with
  | Tsimple z -> never z
  | Tcons c -> Tcons (map_head (close_typ lvl var ix) (close_typ lvl var ix) c)
  | Tvar v -> Tvar (close_typ_var lvl var ix v)
  | Tvjoin (t, v) -> Tvjoin(close_typ lvl var ix t, close_typ_var lvl var ix v)
  | Tpoly {vars; body} -> 
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, close_typ lvl var ix b) vars;
            body = close_typ lvl var ix body}

let close_typ_rigid level ty =
  let close_var = function
    | Vrigid v when Env_level.equal v.level level -> v.var
    | _ -> intfail "close_typ_rigid: not a rigid variable" in
  close_typ level close_var 0 ty

(*
let styp_bot = Scons Bot
let styp_top = Scons Top

(* FIXME: not ident if vars are ⊓ *)
let styp_flexvar fv = Svar (Vflex fv)
let styp_rigvar level var = Svar (Vrigid {level; var})
let styp_boundvar index var = Svar (Vbound {index; var})
let styp_cons cons = Scons cons
*)


let next_flexvar_id = ref 0
let fresh_flexvar_gen level upper : flexvar =
  let id = !next_flexvar_id in
  incr next_flexvar_id;
  { level; upper; lower = { ctor = { cons = Bot; rigvars = [] } ; flexvars = [] }; id;
    pos_visit_count = 0; neg_visit_count = 0; bound_var = -1 }

(*
FIXME del?
module Styp = struct
  let below_level lvl ty =
    assert (ty.bound = []);
    match ty.free with
    | [] -> true
    | Free_vars { level; vars=_ } :: _ ->
       Env_level.extends level lvl &&
         not (Env_level.equal level lvl)

  type repr =
    | Free_vars of { level : env_level; vars: (int, unit) Intlist.t; rest: styp }
    | Cons of styp cons_head

  let mk pol = function
    | Free_vars { level; vars; rest } ->
       assert (below_level level rest);
       assert (not (Intlist.is_empty vars));
       if Intlist.is_empty vars then rest
       else { rest with free = Free_vars {level; vars}::rest.free }
    | Cons cons ->
       styp_cons pol cons

  let de pol ty : repr =
    assert (ty.bound = []);
    assert (ty.pol = pol);
    match ty.free with
    | Free_vars { level; vars } :: free ->
       Free_vars { level; vars; rest = { ty with free } }
    | [] ->
       Cons ty.cons
end
*)

(*
(* FIXME: Make these only work on flex vars *)
let styp_consv level t vars =
  if Intlist.is_empty vars then t
  else Styp.mk t.pol (Free_vars {level; vars; rest=t})

let styp_unconsv lvl t =
  match Styp.de t.pol t with
  | Free_vars { level; vars; rest } when Env_level.equal lvl level ->
     rest, vars
  | _ -> t, Intlist.empty
*)

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


(*
(* Rewrite occurrences of the outermost bound variable *)
let rec map_bound_styp ix rw { cons; vars } =
  let cons = map_head Pos (fun _pol t -> map_bound_styp ix rw t) cons in


  match t.bound with
  | Bound_var { index; sort; var } :: bound when index = ix ->
     assert (sort = sort');
     rw pol var { t with bound; cons }
  | _ -> { t with cons }

let rec map_bound_typ sort ix rw pol = function
  | Tsimple s -> Tsimple (map_bound_styp sort ix rw pol s)
  | Tcons cons -> Tcons (map_head pol (map_bound_typ sort ix rw) cons)
  | Tpoly {names; bounds; flow; body} ->
     let ix = ix + 1 in
     Tpoly {names;
            bounds = Array.map (fun (name, l, u) ->
                name,
                map_bound_styp sort ix rw pol l,
                map_bound_styp sort ix rw (polneg pol) u) bounds;
            flow;
            body = map_bound_typ sort ix rw pol body}

(* Rewrite occurrences of the outermost free variable *)
let rec map_free_styp lvl ix rw pol t =
  assert (t.pol = pol);
  let cons = map_head pol (map_free_styp lvl ix rw) t.cons in
  match t.free with
  | Free_vars {level; vars} :: free when Env_level.equal lvl level ->
     rw pol ix vars { t with free; cons }
  | _ -> { t with cons }

(* FIXME: Tpoly_pos should have separate bounds,
   copied through here.
   That way the rewrite function doesn't need to see poly pos flow.
   IOW: the move to canon bounds (free x cons or bound) breaks the hack that stores flow inline *)
let rec map_free_typ lvl ix rw pol = function
  | Tsimple s -> Tsimple (map_free_styp lvl ix rw pol s)
  | Tcons cons -> Tcons (map_head pol (map_free_typ lvl ix rw) cons)
  | Tpoly {names; bounds; flow; body} ->
     let ix = ix + 1 in
     Tpoly {names;
            bounds = Array.map (fun (name, l, u) ->
                name,
                map_free_styp lvl ix rw pol l,
                map_free_styp lvl ix rw (polneg pol) u) bounds;
            flow;
            body = map_free_typ lvl ix rw pol body}


(* Open a ∀⁺ binder by instantiating its bound variables with fresh flexvars.
   Inserts variables into the current environment (no new level created) *)
let instantiate_flexible env ?(names=SymMap.empty) lvl (vars : (string option * styp * styp) array) (flow : Flow_graph.t) =
  (* The environment already contains ≥0 flexible variables, so we need to
     renumber the new ones to avoid collisions *)
  let tyvars = env_flexvars env lvl in
  let delta = Vector.length tyvars in
  let names = SymMap.map (fun v -> v + delta) names in
  (match env_entry_at_level env lvl with
   (* FIXME hackish *)
   | Eflexible fl ->
      fl.names <- SymMap.union (fun _ _ _ -> assert false) fl.names names;
   | _ -> assert false);
  let disjoint_union v1 v2 =
    Intlist.union (fun _ _ _ -> assert false) v1 v2 in
  let inst _pol v t  =
    styp_consv lvl t (Intlist.singleton (v+delta) ()) in
  vars |> Array.iteri (fun i (name, l, u) ->
    let cons_pos, eps_pos = styp_unconsv lvl l in
    let cons_neg, eps_neg = styp_unconsv lvl u in
    let flow_pos = Intlist.increase_keys delta flow.(i).pred in
    let flow_neg = Intlist.increase_keys delta flow.(i).succ in
    let pos = styp_consv lvl (map_bound_styp Esort_flexible 0 inst Pos cons_pos) (disjoint_union eps_pos flow_pos) in
    let neg = styp_consv lvl (map_bound_styp Esort_flexible 0 inst Neg cons_neg) (disjoint_union eps_neg flow_neg) in
    let v = { name; pos; neg;
              pos_match_cache = ident Pos; neg_match_cache = ident Neg } in
    let id = Vector.push tyvars v in
    assert (id = i + delta);
    (* ensure the ε-invariant is preserved *)
    Intlist.iter eps_pos (fun j () ->
      let vj = Vector.get tyvars j in
      let vjcons, vjflow = styp_unconsv lvl vj.neg in
      vj.neg <- styp_consv lvl vjcons (Intlist.add vjflow id ()));
    Intlist.iter eps_neg (fun j () ->
      let vj = Vector.get tyvars j in
      let vjcons, vjflow = styp_unconsv lvl vj.pos in
      vj.pos <- styp_consv lvl vjcons (Intlist.add vjflow id ()));
    );
  inst

(* NB: a similar invariant-preservation trick needed if ∀⁻ are ever merged.
   Not sure there's any need to do that, though *)

(* Open a ∀⁺ binder, extending env with flexible variables *)
let enter_poly_pos' env names vars flow =
  let level = env_next_level env Esort_flexible in
  let env = env_cons env level (Eflexible {names=SymMap.empty; vars=Vector.create ()}) in
  let inst = instantiate_flexible ~names env level vars flow in
  env, level, inst

let enter_poly_pos env names vars flow body =
  let env, level, inst = enter_poly_pos' env names vars flow in
  env, level, map_bound_typ Esort_flexible 0 inst Pos body

(* Close a ∀⁺ binder, generalising flexible variables *)
let generalise env lvl =
  let gen _pol index vs rest =
    let var, () = Intlist.as_singleton vs in
    { rest with bound = Bound_var {sort=Esort_flexible; index; var} :: rest.bound } in
  let flexvars = env_flexvars env lvl in
  if Vector.length flexvars = 0 then None else
  let bounds_flow = flexvars |> Vector.to_array |> Array.map (fun {pos; neg; _} ->
    let pbound, pflow = styp_unconsv lvl pos in
    let pbound = map_free_styp lvl 0 gen Pos pbound in
    let nbound, nflow = styp_unconsv lvl neg in
    let nbound = map_free_styp lvl 0 gen Neg nbound in
    (* FIXME: name generalised variables? *)
    (None, pbound, nbound), (pflow, nflow)) in
  let bounds = Array.map fst bounds_flow and flow = Array.map snd bounds_flow in
  Some (bounds, Flow_graph.make flow, gen)

*)

(* FIXME: explain why this is OK! *)
(*
let rec mark_principal_styp pol = function
  | Scons cons -> Tcons (map_head pol mark_principal_styp cons)
  | sty -> Tsimple sty

let rec mark_principal pol = function
  | Tcons cons -> Tcons (map_head pol mark_principal cons)
  | Tpoly {names; bounds; body} -> Tpoly {names; bounds; body = mark_principal pol body}
  | Tsimple sty -> mark_principal_styp pol sty
*)

(*
(* Open a ∀⁻ binder, extending env with rigid variables *)
let enter_poly_neg' (env : env) names bounds flow  =
  let rigvar_level = env_next_level env Esort_rigid in
  let inst _pol v t =
    styp_consv rigvar_level t (Intlist.singleton v ()) in
  let vars = bounds |> Array.map (fun (name, l, u) ->
    { name;
      rig_lower = map_bound_styp Esort_rigid 0 inst Neg l;
      rig_upper = map_bound_styp Esort_rigid 0 inst Pos u }) in
  let env = env_cons env rigvar_level (Erigid { names; vars; flow }) in
  env, rigvar_level, inst

let enter_poly_neg env names bounds flow body =
  let env, level, inst = enter_poly_neg' env names bounds flow in
  env, level, map_bound_typ Esort_rigid 0 inst Neg body

let enter_poly pol env names vars flow body =
  match pol with
  | Pos -> enter_poly_pos env names vars flow body
  | Neg -> enter_poly_neg env names vars flow body

let enter_poly' pol env names vars flow =
  match pol with
  | Pos -> enter_poly_pos' env names vars flow
  | Neg -> enter_poly_neg' env names vars flow

*)

(*
 * Well-formedness checks.
 *)

let rec wf_flexvar ~seen env lvl (fv : flexvar) =
  if Hashtbl.mem seen fv.id then () else begin
  Hashtbl.add seen fv.id ();
  if not (Env_level.extends fv.level (env_level env)) then
    intfail "wf_flexvar: fv %d not inside env %d" (Env_level.to_int fv.level) (Env_level.to_int (env_level env));
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
  | UBcons cn ->
     map_ctor_rig (wf_flex_lower_bound ~seen env fv.level) (wf_flexvar ~seen env fv.level) cn |> ignore
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
        (* FIXME: should trim ext somehow, smaller indexes of ext are not valid in t *)
        wf_typ ~seen ~neg ~pos ~ispos env ext t
     | Vflex fv ->
        assert ispos; (* positive *)
        wf_typ ~seen ~neg ~pos ~ispos (env_at_level env fv.level) [] t
     | Vrigid rv ->
        wf_typ ~seen ~neg ~pos ~ispos (env_at_level env rv.level) [] t
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

let wf_ptyp env (t : ptyp) =
  let seen = Hashtbl.create 10 in
  wf_typ ~seen ~neg:(wf_flexvar ~seen env (env_level env)) ~pos:(wf_flex_lower_bound ~seen env (env_level env)) ~ispos:true env [] t
let wf_ntyp env (t : ntyp) =
  let seen = Hashtbl.create 10 in 
  wf_typ ~seen ~neg:(wf_flex_lower_bound ~seen env (env_level env)) ~pos:(wf_flexvar ~seen env (env_level env)) ~ispos:false env [] t



(*

let rec wf_cons pol env wf = function
  | Bot | Top | Bool | Int | String -> ()
  | Record fields ->
     wf_cons_fields pol env wf fields
  | Func (args, res) ->
     wf_cons_fields (polneg pol) env wf args;
     wf pol env res
and wf_cons_fields pol env wf fields =
  let fnames = FieldMap.fold (fun k _ ks -> k::ks) fields.fields [] |> List.rev in
  assert (fnames = List.sort compare fields.fnames);
  FieldMap.iter (fun _k t -> wf pol env t) fields.fields

let rec wf_env = function
  | Env_nil -> ()
  | Env_cons { level; entry; rest } as env ->
     wf_env_entry env level entry;
     begin match rest with
     | Env_nil -> assert (Env_level.to_int level = 0);
     | Env_cons { level=level'; _} ->
        assert ((Env_level.to_int level) = (Env_level.to_int level') + 1);
     end;
     wf_env rest

and wf_match_cache_entry pol' env = function
  | { cons; pol; bound = [];
      free = [Free_vars { level; vars }] } when pol = pol' && cons = ident pol ->
     (*assert (Env_level.equal env.level level);*)
     let v, () = Intlist.as_singleton vars in
     assert (0 <= v && v < Vector.length (env_flexvars env level))
  | _ -> assert false

and wf_env_entry env level = function
  | Evals vs ->
     SymMap.iter (fun _ typ ->  wf_typ Pos env typ) vs
  | Eflexible {names; vars} ->
     assert (names |> SymMap.for_all (fun n i -> (Vector.get vars i).name = Some n));
     Vector.iteri vars (fun _i { name=_; pos; neg; pos_match_cache; neg_match_cache } ->
       wf_styp Pos env pos;
       wf_styp Neg env neg;
       wf_cons Pos env wf_match_cache_entry pos_match_cache;
       wf_cons Neg env wf_match_cache_entry neg_match_cache);
     (* Check the ε-invariant *)
     let head_vars =
       vars |> Vector.to_array
       |> Array.map (fun { pos; neg; _ } ->
              snd (styp_unconsv level pos),
              snd (styp_unconsv level neg)) in
     head_vars |> Array.iteri (fun i (pos, neg) ->
       Intlist.iter pos (fun j () ->
         assert (Intlist.contains (snd head_vars.(j)) i));
       Intlist.iter neg (fun j () ->
         assert (Intlist.contains (fst head_vars.(j)) i)))
  | Erigid { names; vars; flow } ->
     assert (Flow_graph.length flow = Array.length vars);
     assert (names |> SymMap.for_all (fun n i -> vars.(i).name = Some n));
     vars |> Array.iter (fun { name=_; rig_lower; rig_upper } ->
       wf_styp Neg env rig_lower;
       wf_styp Pos env rig_upper;
       assert (snd (styp_unconsv level rig_lower) = Intlist.empty);
       assert (snd (styp_unconsv level rig_upper) = Intlist.empty))

and wf_styp_gen : 'a . (polarity -> 'a -> (int, unit) Intlist.t -> unit) -> polarity -> 'a gen_env -> styp -> unit
  = fun wf_vars pol env t ->
  assert (t.pol = pol);
  assert (t.bound = []);
  t.free |> List.iter (fun (Free_vars { level; vars }) ->
     Intlist.wf vars;
     assert (not (Intlist.is_empty vars));
     wf_vars pol (env_entry_at_level env level) vars);
  wf_cons pol env (wf_styp_gen wf_vars) t.cons;

and wf_styp pol env t = wf_styp_gen wf_vars pol env t

and wf_typ pol env = function
  | Tcons cons ->
     wf_cons pol env wf_typ cons
  | Tsimple s ->
     wf_styp pol env s
  | Tpoly {names; bounds; flow; body} ->
     assert (Flow_graph.length flow = Array.length bounds);
     (* toplevel references to bound variables should be in flow, not bounds *)
     bounds |> Array.iter (fun (_name, p, n) ->
       assert (p.bound = []); assert (n.bound = []));
     let env, level, body = enter_poly pol env names bounds flow body in
     wf_env_entry env level (env_entry_at_level env level);
     wf_typ pol env body

and wf_vars _pol entry vs =
  let len =
    match entry with
    | Eflexible {vars; _} -> Vector.length vars
    | Erigid { vars; _ } -> Array.length vars
    | _ -> assert false in
  Intlist.iter vs (fun v () -> assert (0 <= v && v < len))

(*
 * Printing of internal representations
 *)

open PPrint
let str = utf8string
let rec pr_cons pol pr t =
  match t with
  | Bot -> str "⊥"
  | Top -> str "⊤"
  | Bool -> str "bool"
  | Int -> str "int"
  | String -> str "string"
  | Record fs -> pr_cons_fields pol pr fs
  | Func (args, res) ->
     pr_cons_fields (polneg pol) pr args ^^
       blank 1 ^^ str "→" ^^ blank 1 ^^
         pr pol res
and pr_cons_fields pol pr fields =
  let named_fields = fields.fnames |> List.map (fun k ->
    (match k with
     | Field_named s -> str s ^^ str ":" ^^ blank 1
     | Field_positional _ -> empty) ^^ pr pol (FieldMap.find k fields.fields)) in
  let cl = match fields.fopen with `Closed -> [] | `Open -> [str "..."] in
  parens (group (nest 2 (break 0 ^^ separate (comma ^^ break 1) (named_fields @ cl))))

let rec pr_styp pol t =
  let free =
    t.free |> List.concat_map (fun (Free_vars { level; vars }) ->
      vars |> Intlist.to_list |> List.map (fun (v, ()) ->
        (Env_level.sort level, Printf.sprintf "#%d.%d" (Env_level.to_int level) v))) in
  let bound =
    t.bound |> List.map (fun (Bound_var {index; sort; var}) ->
      sort, Printf.sprintf ".%d.%d" index var) in
  let vars = free @ bound in
  if vars = [] then
    pr_cons pol pr_styp t.cons
  else
    let join = match pol with Pos -> "⊔" | Neg -> "⊓" in
    let join = blank 1 ^^ str join ^^ blank 1 in
    let pv (_,v) = string v in
    let pvars = separate_map join pv vars in
    if t.cons = ident pol then
      pvars
    else
      pr_cons pol pr_styp t.cons ^^ join ^^ pvars

let rec pr_typ pol = function
  | Tsimple s -> pr_styp pol s
  | Tcons cons -> pr_cons pol pr_typ cons
  | Tpoly {names=_; bounds; flow; body} ->
     str "∀" ^^ (match pol with Pos -> str "⁺" | Neg -> str "⁻") ^^ blank 1 ^^
       separate_map (str "," ^^ blank 1) (pr_bound pol) (Array.to_list bounds |> List.mapi (fun i x -> i,x)) ^^
         (Flow_graph.fold (fun acc n p ->
             acc ^^ comma ^^ break 1 ^^ str (Printf.sprintf "%d ≤ %d" n p)) flow empty) ^^
         str "." ^^ blank 1 ^^ pr_typ pol body

and pr_bound pol (ix, (_name, lower, upper)) =
  str (Printf.sprintf "%d:" ix) ^^
  brackets (pr_styp pol lower ^^
              str "," ^^
            pr_styp (polneg pol) upper)


let rec pr_env =
  function
  | Env_nil -> empty
  | Env_cons { level; entry; rest} ->
  let doc =
    match rest with
    | Env_nil -> empty
    | env -> pr_env env ^^ comma ^^ break 1 in
  match entry with
  | Evals v when SymMap.is_empty v ->
     (match rest with Env_nil -> empty | _ -> pr_env rest)
  | Eflexible {vars; _} when Vector.length vars = 0 ->
     (match rest with Env_nil -> empty | _ -> pr_env rest)
  | Evals _ -> doc ^^ string (Printf.sprintf "<vals %d>" (Env_level.to_int level)) (*failwith "pr_env unimplemented for Evals"*)
  | Eflexible vars ->
    Vector.fold_lefti (fun doc i v ->
      doc ^^ str (Printf.sprintf "%d" i) ^^ str ":" ^^ blank 1 ^^
        str "[" ^^ pr_styp Pos v.pos ^^ comma ^^ blank 1 ^^ pr_styp Neg v.neg ^^ str "]" ^^
          comma ^^ break 1) doc vars.vars
  | Erigid {names=_;vars;flow} ->
     doc ^^
       separate_map (str "," ^^ blank 1) (pr_bound Neg) (Array.to_list vars |> List.mapi (fun i (x:rigvar) -> i,(x.name,x.rig_lower,x.rig_upper))) ^^
         (Flow_graph.fold (fun acc n p ->
             acc ^^ comma ^^ break 1 ^^ str (Printf.sprintf "%d ≤ %d" n p)) flow empty)



let func a b = Func (collect_fields [Fpos a], b)

let bvar pol sort index var =
  styp_bvar pol sort index var

let test () =
  let level = env_next_level Env_nil Esort_flexible in
  let env = env_cons Env_nil level (Eflexible {vars=Vector.create ();names=SymMap.empty}) in
  let choose1_pos =
    Tpoly {names=SymMap.empty;
           bounds =[| Some "A", styp_bot Pos, styp_top Neg;
                      Some "B", styp_bot Pos, styp_top Neg;
                      Some "C", styp_bot Pos, styp_top Neg |];
           flow=Flow_graph.of_list 3 [(0,2); (1,2)];
           body=Tsimple (styp_cons Pos (func
                 (bvar Neg Esort_flexible 0 0)
                 (styp_cons Pos (func
                   (bvar Neg Esort_flexible 0 1)
                   (bvar Pos Esort_flexible 0 2)))))} in
  wf_typ Pos env choose1_pos;
  PPrint.ToChannel.pretty 1. 80 stdout
    (pr_typ Pos choose1_pos ^^ hardline);
  let nested =
    Tpoly {names=SymMap.empty;
           bounds=[| Some "A", styp_bot Pos, styp_top Neg |];
           flow=Flow_graph.of_list 1 [];
           body=Tpoly {names=SymMap.empty;
                       bounds=[| Some "B", styp_bot Pos, bvar Neg Esort_flexible 1 0 |];
                       flow=Flow_graph.of_list 1 [];
                       body=Tsimple (bvar Pos Esort_flexible 0 0)}} in
  wf_typ Pos env nested;
  PPrint.ToChannel.pretty 1. 80 stdout
    (pr_env env ^^ str " ⊢ " ^^ pr_typ Pos nested ^^ hardline);
  let body =
    match nested with
    | Tpoly {names=_; bounds; flow; body} ->
       let inst = instantiate_flexible env level bounds flow in
       map_bound_typ Esort_flexible 0 inst Pos body
    | _ -> assert false in
  PPrint.ToChannel.pretty 1. 80 stdout
    (group (pr_env env) ^^ str " ⊢ " ^^ pr_typ Pos body ^^ hardline);
  wf_env env; wf_typ Pos env body;
  let body =
    match body with
    | Tpoly {names=_; bounds; flow; body} ->
       let inst = instantiate_flexible env level bounds flow in
       map_bound_typ Esort_flexible 0 inst Pos body
    | _ -> assert false in
  PPrint.ToChannel.pretty 1. 80 stdout
    (group (pr_env env) ^^ str " ⊢ " ^^ pr_typ Pos body ^^ hardline);
  wf_env env; wf_typ Pos env body

*)

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

let flexvar_name fv =
  let names = [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "κ"; "ν"; "ξ"; "π"; "ρ" |] in
  let id = fv.id in
  if id < Array.length names then names.(id)
  else Printf.sprintf "_%d" (id - Array.length names)

let unparse_rigid_var {level;var} =
  mktyexp (named_type (Printf.sprintf "%d.%d" (Env_level.to_int level) var))

let unparse_flexvar ~flexvar fv =
  flexvar fv; mktyexp (named_type (flexvar_name fv))

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
     (* FIXME name the variables! *)
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
    if not (taken name) then name else freshen name 1 in
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
