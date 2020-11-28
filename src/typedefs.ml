(*
 * Core definitions used by the typechecker
 *)

module StrMap = Map.Make (struct type t = string let compare = compare end)

open Tuple_fields

type polarity = Pos | Neg

(* Head type constructors. These do not bind type variables. *)
type +'a cons_head =
  | Top
  | Bot
  (* FIXME: maybe delete these once abstypes exist? *)
  | Bool
  | Int
  | String
  | Record of 'a tuple_fields
  | Func of 'a tuple_fields * 'a

module Env_level : sig
  type 'sort t

  val initial : 's -> 's t

  val extend : 's t -> 's -> 's t
  val replace : 's t -> 's -> 's t

  val equal : 's t -> 's t -> bool
  val extends : 's t -> 's t -> bool

  val to_int : 's t -> int

  val sort : 's t -> 's
end = struct
  (* Not actually mutable, but marking it as such
     makes physical equality work *)
  type 'sort t =
    { mutable level : int;
      sort : 'sort }

  let initial sort = { level = 0; sort }
  let extend { level; _ } sort = { level = level + 1; sort }
  let replace { level; sort=_ } sort = { level; sort }

  let extends {level=l1;sort=_} {level=l2;sort=_} = l1 <= l2

  let equal l1 l2 =
    if l1.level = l2.level then
      (assert (l1 == l2); true)
    else
      false

  let to_int l = l.level
  let sort l = l.sort
end

type env_sort = Esort_vals | Esort_flexible | Esort_rigid
type env_level = env_sort Env_level.t

type 'a gen_env =
  | Env_cons of { level : env_sort Env_level.t;
                  entry : 'a;
                  rest : 'a gen_env }
  | Env_nil

(* Entries in the typing environment *)
type env_entry =
  (* Binding x : τ *)
  | Evals of typ SymMap.t
  (* Flexible variables (inferred polymorphism, instantiated ∀⁺) *)
  | Eflexible of { mutable names : int SymMap.t; vars : flexvar Vector.t }
  (* Rigid type variables (abstract types, checked forall) *)
  | Erigid of {
      (* all fields immutable, despite array/table *)
      (* FIXME: explain why predicativity matters here *)
      names : int SymMap.t;
      vars : rigvar array;
      flow : Flow_graph.t;
    }

and env = env_entry gen_env

(* Simple types (the result of inference). No binders. *)
and styp =
  | Cons of { pol: polarity; cons: styp cons_head }
  | Free_vars of { level: env_level; vars: (int, unit) Intlist.t; rest: styp }
  | Bound_var of { pol: polarity; index: int; sort: env_sort; var: int }

(* Flexible type variables.
   Maintain the ε-invariant:
   for flexible variables α, β from the same binding group,
   β ∈ α.pos.tyvars iff α ∈ β.neg.tyvars *)
and flexvar = {
    name : string option;
    (* positive component, lower bound *)
    mutable pos : styp;
    (* negative component, upper bound *)
    mutable neg : styp;

    (* Match cache styps are either ident or a single flexible variable at the same level *)
    (* FIXME: should be an int or var cons_head?  *)
    mutable pos_match_cache : styp cons_head;
    mutable neg_match_cache : styp cons_head;
  }

(* Rigid type variables.
   Maintain the head-invariant:
   the bounds of a rigid variable a do not mention other variables
   from the same binding group except under type constructors *)
and rigvar = {
  (* unique among a binding group, but can shadow.
     Only used for parsing/printing: internally, referred to by index. *)
  name : string option;
  (* lower bound / negative component *)
  rig_lower : styp;
  (* upper bound / positive component *)
  rig_upper : styp;
}

(* General polymorphic types.  Inference may produce these after
   generalisation, but never instantiates a variable with one. *)
and typ =
  | Tsimple of styp
  | Tcons of typ cons_head
  (* Forall *)
  (* FIXME: maybe change to (poly, body)? *)
  | Tpoly of {
    names : int SymMap.t;  (* may be incomplete *)
    bounds : (string option * styp * styp) array;
    flow : Flow_graph.t;
    body : typ }

let polneg = function Pos -> Neg | Neg -> Pos

(* Underconstrained. Might be anything. Identity of meet/join. *)
let ident = function
  | Pos -> Bot
  | Neg -> Top

(* Overconstrained. Must be everything. Annihilator of meet/join. *)
let annih = function
  | Pos -> Top
  | Neg -> Bot

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

let env_sort_of_entry = function
  | Evals _ -> Esort_vals
  | Erigid _ -> Esort_rigid
  | Eflexible _ -> Esort_flexible

let env_next_level env sort =
  match env with
  | Env_nil -> Env_level.initial sort
  | Env_cons { level; _ } -> Env_level.extend level sort

let env_cons rest level entry =
  assert (Env_level.sort level = env_sort_of_entry entry);
  Env_cons { level; entry; rest }

let env_cons_entry rest entry =
  Env_cons { level = env_next_level rest (env_sort_of_entry entry);
             entry;
             rest }

let env_replace env level newlevel entry =
  assert (Env_level.to_int level = Env_level.to_int newlevel);
  match env with
  | Env_cons {level=l; entry=_; rest} when Env_level.equal level l ->
     Env_cons {level=newlevel; entry; rest}
  | _ -> assert false

let env_flexvars env lvl =
  match env_entry_at_level env lvl with
  | Eflexible {vars;_} -> vars
  | _ -> failwith "error: no flexible vars here"

let env_rigid_vars env lvl =
  match env_entry_at_level env lvl with
  | Erigid r -> (r.vars, r.flow)
  | _ -> failwith "error: no rigid vars here"

let env_rigid_flow env lvl i j =
  let vars, flow = env_rigid_vars env lvl in
  assert (0 <= i && i < Array.length vars);
  assert (0 <= j && j < Array.length vars);
  Flow_graph.mem flow i j

let vlist_union v1 v2 =
  Intlist.union (fun _ () () -> ()) v1 v2
  

(*
 * Opening/closing of binders
 *)


let map_head_cons pol f fields =
  map_fields (fun _fn x -> f pol x) fields

let map_head pol f = function
  | Top -> Top
  | Bot -> Bot
  | Bool -> Bool
  | Int -> Int
  | String -> String
  | Record fields -> Record (map_head_cons pol f fields)
  | Func (args, res) ->
     Func (map_head_cons (polneg pol) f args, f pol res)

let cons_typ _pol cons = Tcons cons


let styp_pos_bot = Cons {pol=Pos; cons=Bot}
let styp_neg_bot = Cons {pol=Neg; cons=Bot}
let styp_bot = function Pos -> styp_pos_bot | Neg -> styp_neg_bot
let styp_pos_top = Cons {pol=Pos; cons=Top}
let styp_neg_top = Cons {pol=Neg; cons=Top}
let styp_top = function Pos -> styp_pos_top | Neg -> styp_neg_top

let styp_trivial pol = Cons {pol; cons=ident pol}

let is_trivial pol = function
  | Cons { pol=pol'; cons } -> assert (pol = pol'); cons = ident pol
  | Free_vars _ | Bound_var _ -> false

let styp_vars pol level vars =
  Free_vars { level; vars; rest = styp_trivial pol }
let styp_var pol level var =
  styp_vars pol level (Intlist.singleton var ())
let styp_cons pol cons =
  Cons {pol; cons}

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

let lookup_named_type = function
  | "any" -> Some Top
  | "nothing" -> Some Bot
  | "bool" -> Some Bool
  | "int" -> Some Int
  | "string" -> Some String
  | _ -> None

let binder_sort = function
  | Pos -> Esort_flexible
  | Neg -> Esort_rigid

(* Rewrite occurrences of the outermost bound variable *)
let rec map_bound_styp sort' ix rw pol' = function
  | Cons { pol; cons } ->
     assert (pol = pol');
     Cons { pol; cons = map_head pol (map_bound_styp sort' ix rw) cons }
  | Free_vars { level; vars; rest } ->
     Free_vars { level; vars; rest = map_bound_styp sort' ix rw pol' rest }
  | Bound_var { pol; sort; index; var } when index = ix ->
     assert (pol = pol'); assert (sort = sort');
     rw pol var
  | Bound_var _ as ty -> ty

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
let rec map_free_styp lvl ix rw pol' = function
  | Bound_var _ as ty -> ty
  | Cons { pol; cons } ->
     assert (pol = pol');
     Cons { pol; cons = map_head pol (map_free_styp lvl ix rw) cons }
  | Free_vars { level; vars; rest } ->
     assert (Env_level.extends level lvl);
     let rest = map_free_styp lvl ix rw pol' rest in
     if Env_level.equal lvl level then
       rw pol' ix vars rest
     else
       Free_vars { level; vars; rest }

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


(* FIXME: use these more *)
let styp_consv level t vars =
  (* FIXME: add a wf_styp_at_level here? *)
  if Intlist.is_empty vars then t
  else Free_vars { level; vars; rest = t }

let styp_unconsv lvl = function
  (* FIXME: add a wf_styp_at_level here? *)
  | Free_vars { level; vars; rest } when Env_level.equal lvl level ->
     rest, vars
  | t -> t, Intlist.empty

type styp_unconsv2_result =
  | Cons2 of { a: styp cons_head; b: styp cons_head }
  | Vars2 of { level: env_level;
               a: styp; va: (int, unit) Intlist.t;
               b: styp; vb: (int, unit) Intlist.t }

let styp_unconsv2 a b =
  match a, b with
  | (Bound_var _, _) | (_, Bound_var _) -> assert false
  | Cons {pol=_; cons=a}, Cons {pol=_; cons=b} ->
     Cons2 {a;b}
  | Free_vars { level; vars=va; rest=a }, Cons _ ->
     Vars2 {level; a; va; b; vb = Intlist.empty}
  | Cons _, Free_vars { level; vars=vb; rest=b } ->
     Vars2 {level; a; va=Intlist.empty; b; vb }
  | Free_vars {level; vars=va; rest=a},
    Free_vars {level=level'; vars=vb; rest=b}
       when Env_level.equal level level' ->
     Vars2 {level; a; va; b; vb}
  | Free_vars {level=la; vars=va; rest=ra},
    Free_vars {level=lb; vars=vb; rest=rb} ->
     if Env_level.extends la lb then
       Vars2 {level=lb; a; va=Intlist.empty; b=rb; vb}
     else
       Vars2 {level=la; a=ra; va; b; vb=Intlist.empty}

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
  let inst pol v =
    styp_vars pol lvl (Intlist.singleton (v+delta) ()) in
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
  let gen pol index vs rest =
    let var, () = Intlist.as_singleton vs in
    assert (is_trivial pol rest);
    Bound_var {pol; sort=Esort_flexible; index; var} in
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

(* FIXME: explain why this is OK! *)
let rec mark_principal_styp pol' = function
  | Cons { pol; cons } -> assert (pol=pol'); Tcons (map_head pol mark_principal_styp cons)
  | sty -> Tsimple sty

let rec mark_principal pol = function
  | Tcons cons -> Tcons (map_head pol mark_principal cons)
  | Tpoly {names; bounds; flow; body} -> Tpoly {names; bounds; flow; body = mark_principal pol body}
  | Tsimple sty -> mark_principal_styp pol sty

(* Open a ∀⁻ binder, extending env with rigid variables *)
let enter_poly_neg' (env : env) names bounds flow  =
  let rigvar_level = env_next_level env Esort_rigid in
  let inst pol v =
    styp_vars pol rigvar_level (Intlist.singleton v ()) in
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

(*
 * Well-formedness checks.
 * The wf_foo functions also check for local closure.
 *)

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

and wf_match_cache_entry pol env = function
  | Free_vars { level; vars; rest} when is_trivial pol rest ->
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
 = fun wf_vars pol' env -> function
  | Bound_var _ -> assert false (* locally closed *)
  | Cons { pol; cons } ->
     assert (pol = pol');
     wf_cons pol env (wf_styp_gen wf_vars) cons
  | Free_vars { level; vars; rest } ->
     Intlist.wf vars;
     assert (not (Intlist.is_empty vars));
     wf_vars pol' (env_entry_at_level env level) vars;
     wf_styp_gen wf_vars pol' env rest

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
       (match p with Bound_var _ -> assert false | _ -> ());
       (match n with Bound_var _ -> assert false | _ -> ()));
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

let rec pr_styp pol = function
  | Bound_var { pol=_; sort=_; index; var } ->
     string (Printf.sprintf ".%d.%d" index var)
  | Cons { pol=_; cons } ->
     pr_cons pol pr_styp cons
  | Free_vars { level; vars; rest } ->
     let join = match pol with Pos -> "⊔" | Neg -> "⊓" in
     let join = blank 1 ^^ str join ^^ blank 1 in
     let pv (v, ()) = Printf.sprintf "#%d.%d" (Env_level.to_int level) v |> string in
     let pvars = separate_map join pv (Intlist.to_list vars) in
     if is_trivial pol rest then
       pvars
     else
       pr_styp pol rest ^^ join ^^ pvars

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
  Bound_var {pol; sort; index; var}

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
  
