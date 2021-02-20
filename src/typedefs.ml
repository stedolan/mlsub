(*
 * Core definitions used by the typechecker
 *)

module StrMap = Map.Make (struct type t = string let compare = compare end)

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

  val initial : unit -> t

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

  let initial () = { level = 0 }
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
   Their bounds are stored in the environment (FIXME: should they be?) *)
type rigvar =
  { level: env_level;
    var: int }

(* A ctor_ty is a join of a constructed type and some rigid variables *)
type ('neg,'pos) ctor_ty =
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
    mutable neg_visit_count : int }

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



type polarity = Pos | Neg


(* Simple types (the result of inference). No binders.

   There are some rules about joins:
    - No bound variables in contravariant joins
    - No flexible variables in negative joins
    - At most one Scons in negative or contravariant joins
 *)


type styp =
  | Scons of (styp, styp) cons_head
  | Sjoin of styp * styp
  | Svar of styp_var

and styp_var =
  | Vrigid of rigvar
  | Vflex of flexvar
  | Vbound of { index: int; var: int }

(* FIXME:
try something more like this:

type boundvar = { index: int; var: int }
type styp =
  { scons: (styp, styp) ctor_ty; sflex: flexvar list; sbound: boundvar list }
*)


(* General polymorphic types.  Inference may produce these after
   generalisation, but never instantiates a variable with one. *)
type typ =
  | Tsimple of styp
  | Tcons of (typ,typ) cons_head
  (* Forall *)
  (* FIXME: maybe change to (poly, body)? *)
  | Tpoly of {
    names : int SymMap.t;  (* may be incomplete *)
    bounds : styp array;   (* FIXME names? *)
    body : typ }


(* Entries in the typing environment *)
type env_entry =
  (* Binding x : τ *)
  | Evals of typ SymMap.t
  (* Flexible variables (inferred polymorphism, instantiated ∀⁺)
     FIXME: should these have a separate environment entry at all? *)
  | Eflexible
  (* Rigid type variables (abstract types, checked forall) *)
  | Erigid of {
      (* all fields immutable, despite array/table *)
      (* FIXME: explain why predicativity matters here *)
      names : int SymMap.t;
      vars : rigvar_defn array;
    }


and env =
  | Env_cons of { level : env_level;
                  entry : env_entry;
                  rest : env }
  | Env_nil



(* Rigid type variables.
   Maintain the head-invariant:
   the bounds of a rigid variable a do not mention other variables
   from the same binding group except under type constructors *)
and rigvar_defn = {
  (* unique among a binding group, but can shadow.
     Only used for parsing/printing: internally, referred to by index. *)
  name : string option;
  upper : (flexvar, flex_lower_bound) ctor_ty;
}

let polneg = function Pos -> Neg | Neg -> Pos

(*
 * Environment ordering
 *)

let assert_env_equal env1 env2 =
  match env1, env2 with
  | Env_nil, Env_nil -> ()
  | Env_cons { level=l1; _ }, Env_cons { level=l2; _ } ->
     assert (Env_level.equal l1 l2)
  | _ -> assert false

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

let env_rigid_vars env lvl =
  match env_entry_at_level env lvl with
  | Erigid r -> r.vars
  | _ -> failwith "error: no rigid vars here"

let env_rigid_bound env lvl var =
  (env_rigid_vars env lvl).(var).upper

(*
 * Opening/closing of binders
 *)


let map_head_cons pol f fields =
  map_fields (fun _fn x -> f pol x) fields

let cons_typ _pol cons = Tcons cons

let styp_bot = Scons Bot
let styp_top = Scons Top

(* FIXME: not ident if vars are ⊓ *)
let styp_flexvar fv = Svar (Vflex fv)
let styp_rigvar level var = Svar (Vrigid {level; var})
let styp_boundvar index var = Svar (Vbound {index; var})
let styp_cons cons = Scons cons

let next_flexvar_id = ref 0
let fresh_flexvar level : flexvar =
  let id = !next_flexvar_id in
  incr next_flexvar_id;
  { level; upper = UBnone; lower = { ctor = { cons = Bot; rigvars = [] } ; flexvars = [] }; id;
    pos_visit_count = 0; neg_visit_count = 0 }


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
 * The wf_foo functions also check for local closure.
 *)

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


let loc : Exp.location =
 { source = "<none>";
   loc_start = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0};
   loc_end = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0} }

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, loc)

let rec unparse_styp' ~flexvar = function
  | Scons Top -> named_type "any"
  | Scons Bot -> named_type "nothing"
  | Scons Bool -> named_type "bool"
  | Scons Int -> named_type "int"
  | Scons String -> named_type "string"
  | Scons Record fs ->
     Trecord (Tuple_fields.map_fields (fun _ t -> unparse_styp ~flexvar t) fs)
  | Scons Func (args, ret) ->
     Tfunc (Tuple_fields.map_fields (fun _ t -> unparse_styp ~flexvar t) args,
            unparse_styp ~flexvar ret)
  | Sjoin (a, b) ->
     let a = unparse_styp ~flexvar a in
     let b = unparse_styp ~flexvar b in
     Tjoin (a, b)
  | Svar (Vbound _) -> failwith "unparse: vbound"
  | Svar (Vrigid _) -> failwith "unparse: vrigid"
  | Svar (Vflex fv) -> flexvar fv
       
and unparse_styp ~flexvar t =
  Some (unparse_styp' ~flexvar t), loc


let flexvar_name fv =
  let names = [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "κ"; "ν"; "ξ"; "π"; "ρ" |] in
  let id = fv.id in
  if id < Array.length names then names.(id)
  else Printf.sprintf "_%d" (id - Array.length names)
