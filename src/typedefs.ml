(*
 * Core definitions used by the typechecker
 *)

module IntMap = Map.Make (struct type t = int let compare = compare end)
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

module Env_marker = struct
  type t = unit ref
  let make () = ref ()
  let assert_equal (x : t) (y : t) =
    assert (x == y)
end

module Env_level = struct
  type t = int

  let empty = 0
  let extend l = l + 1

  let extends env1 env2 = env1 <= env2
  let equal env1 env2 = (env1 = env2)
end


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

and env =
  { level : Env_level.t;
    marker : Env_marker.t;
    entry : env_entry;
    rest : env option }

(* Simple types (the result of inference). No binders. *)
and styp =
  { body: styp_body; pol: polarity }

and styp_body =
  | Styp of { cons : styp cons_head; tyvars : vset }
  | Bound_var of { index : int; var : int }

and vset = (Env_level.t, Env_marker.t * (int, unit) Intlist.t) Intlist.t

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
    (* FIXME: should be an int or vset cons_head?  *)
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

let is_trivial pol { body; pol = pol' } =
  assert (pol = pol');
  match body with
  | Styp {cons; tyvars} ->
     cons = ident pol && Intlist.is_empty tyvars
  | Bound_var _ -> assert false

(* Overconstrained. Must be everything. Annihilator of meet/join. *)
let annih = function
  | Pos -> Top
  | Neg -> Bot

(*
 * Environment ordering and vset merging
 *)

let assert_env_equal env1 env2 =
  Env_marker.assert_equal env1.marker env2.marker

let rec env_at_level env lvl mark =
  assert (Env_level.extends lvl env.level);
  if Env_level.equal env.level lvl then
    (Env_marker.assert_equal env.marker mark; env)
  else
    match env.rest with
    | None -> assert false
    | Some rest -> env_at_level rest lvl mark

(* must be an env (lvl,mark) *)
let env_entry_at_level env lvl mark =
  (env_at_level env lvl mark).entry

(* Check that one environment is an extension of another *)
let assert_env_prefix env ext =
  ignore (env_entry_at_level env ext.level ext.marker)

(*

(* Only defined if one environment is an extension of the other *)
let env_max e1 e2 =
  match e1, e2 with
  | Env_empty, e | e, Env_empty -> e
  | Env_cons { level = l1; _ }, Env_cons { level = l2; _ } ->
     if l1 = l2 then
       (assert (e1 == e2); e1)
     else if l1 < l2 then
       (assert_env_prefix e1 e2; e2)
     else
       (assert_env_prefix e2 e1; e1)
*)

let env_cons env entry =
  { level = Env_level.extend env.level;
    marker = Env_marker.make ();
    entry;
    rest = Some env }

let env_flexvars env lvl mark =
  match env_entry_at_level env lvl mark with
  | Eflexible {vars;_} -> vars
  | _ -> failwith "error: no flexible vars here"

let env_rigid_vars env lvl mark =
  match env_entry_at_level env lvl mark with
  | Erigid r -> (r.vars, r.flow)
  | _ -> failwith "error: no rigid vars here"

let env_rigid_flow env lvl mark i j =
  let vars, flow = env_rigid_vars env lvl mark in
  assert (0 <= i && i < Array.length vars);
  assert (0 <= j && j < Array.length vars);
  Flow_graph.mem flow i j

let vlist_union v1 v2 =
  Intlist.union (fun _ () () -> ()) v1 v2

let vset_union vars1 vars2 =
  Intlist.union (fun _ (m1, v1) (m2, v2) ->
      Env_marker.assert_equal m1 m2;
      m1, vlist_union v1 v2) vars1 vars2

(*
let rec vset_lookup venv vsort = function
  | VSnil -> []
  | VScons { env; sort; vars; _ }
       when env == venv && sort = vsort ->
     vars
  | VScons { env; rest; _ } ->
     if env_level env < env_level venv then []
     else vset_lookup venv vsort rest
*)

(*
let styp_uncons venv vsort ({ tyvars; cons; pol } as t) =
  match tyvars with
  | VSnil -> t, []
  | VScons { env; sort; vars; rest }
    when env == venv && sort = vsort ->
     { tyvars = rest; cons; pol }, vars
  | VScons { env; sort; _ } ->
     assert_env_prefix env venv;
     assert (env_level env < env_level venv
             || (sort = Rigid && vsort = Flexible));
     t, []
*)


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

let cons_styp pol tyvars cons = { pol; body = Styp {cons; tyvars} }
let cons_typ _pol cons = Tcons cons


(* Rewrite occurrences of the outermost bound variable *)
let rec map_bound_styp ix rw pol' ({ body; pol } as ty) =
  assert (pol = pol');
  match body with
  | Styp { cons; tyvars } ->
     { body = Styp { cons = map_head pol (map_bound_styp ix rw) cons;
                     tyvars }; pol }
  | Bound_var { index; var } when index = ix ->
     rw pol var
  | Bound_var _ -> ty

let rec map_bound_typ ix rw pol = function
  | Tsimple s -> Tsimple (map_bound_styp ix rw pol s)
  | Tcons cons -> Tcons (map_head pol (map_bound_typ ix rw) cons)
  | Tpoly {names; bounds; flow; body} ->
     let ix = ix + 1 in
     Tpoly {names;
            bounds = Array.map (fun (name, l, u) ->
                name,
                map_bound_styp ix rw pol l,
                map_bound_styp ix rw (polneg pol) u) bounds;
            flow;
            body = map_bound_typ ix rw pol body}

(* Rewrite occurrences of the outermost free variable *)
let rec map_free_styp lvl mark ix rw pol' ({ body; pol } as ty) =
  assert (pol = pol');
  match body with
  | Bound_var _ -> ty
  | Styp { cons; tyvars } ->
     let cons = map_head pol (map_free_styp lvl mark ix rw) cons in
     match Intlist.peel_max lvl tyvars with
     | None -> { body = Styp { cons; tyvars }; pol }
     | Some (vs, tyvars') ->
        let rest = { body = Styp { cons; tyvars = tyvars' }; pol } in
        rw pol ix vs rest

(* FIXME: Tpoly_pos should have separate bounds,
   copied through here. 
   That way the rewrite function doesn't need to see poly pos flow.
   IOW: the move to canon bounds (free x cons or bound) breaks the hack that stores flow inline *)
let rec map_free_typ lvl mark ix rw pol = function
  | Tsimple s -> Tsimple (map_free_styp lvl mark ix rw pol s)
  | Tcons cons -> Tcons (map_head pol (map_free_typ lvl mark ix rw) cons)
  | Tpoly {names; bounds; flow; body} ->
     let ix = ix + 1 in
     Tpoly {names;
            bounds = Array.map (fun (name, l, u) ->
                name,
                map_free_styp lvl mark ix rw pol l,
                map_free_styp lvl mark ix rw (polneg pol) u) bounds;
            flow;
            body = map_free_typ lvl mark ix rw pol body}


(* FIXME: use these more *)
let styp_consv lvl mark ({ body; pol } as t) vs =
  (* FIXME: add a wf_styp_at_level here? *)
  if Intlist.is_empty vs then t else
    match body with
    | Bound_var _ -> assert false (* should be at-or-below lvl, bound variables aren't *)
    | Styp { cons; tyvars } ->
       let tyvars = Intlist.cons_max tyvars lvl (mark, vs) in
       { body = Styp { cons; tyvars };  pol }

let styp_unconsv lvl mark ({ body; pol } as t) =
  (* FIXME: add a wf_styp_at_level here? *)
  match body with
  | Bound_var _ -> assert false (* should be below lvl, bound variables aren't *)
  | Styp { cons; tyvars } ->
     match Intlist.peel_max lvl tyvars with
     | None -> t, Intlist.empty
     | Some ((mark', vs), rest) ->
        (* FIXME FIXME bug here, this is nonsense. Should hit the case above.
           Let's see if testing hits this. Might need nested scopes first *)
        Env_marker.assert_equal mark mark';
        { body = Styp { cons; tyvars = rest }; pol }, vs

let styp_max_var_level {body; pol=_} =
  match body with
  | Bound_var _ ->
     assert false
  | Styp { cons=_; tyvars } ->
     match Intlist.take_max tyvars with
     | Empty -> None
     | Cons (lvl, (mark, _), _) -> Some (lvl, mark)

(* Open a ∀⁺ binder by instantiating its bound variables with fresh flexvars.
   Inserts variables into the current environment (no new level created) *)
let instantiate_flexible env ?(names=SymMap.empty) lvl mark (vars : (string option * styp * styp) array) (flow : Flow_graph.t) (body : typ) =
  (* The environment already contains ≥0 flexible variables, so we need to
     renumber the new ones to avoid collisions *)
  let tyvars = env_flexvars env lvl mark in
  let delta = Vector.length tyvars in
  let names = SymMap.map (fun v -> v + delta) names in
  (match env_entry_at_level env lvl mark with
   (* FIXME hackish *)
   | Eflexible fl ->
      fl.names <- SymMap.union (fun _ _ _ -> assert false) fl.names names;
   | _ -> assert false);
  let disjoint_union v1 v2 =
    Intlist.union (fun _ _ _ -> assert false) v1 v2 in
  let inst pol v =
    cons_styp pol (Intlist.singleton lvl (mark, Intlist.singleton (v+delta) ())) (ident pol) in
  vars |> Array.iteri (fun i (name, l, u) ->
    let cons_pos, eps_pos = styp_unconsv lvl mark l in
    let cons_neg, eps_neg = styp_unconsv lvl mark u in
    let flow_pos = Intlist.increase_keys delta flow.(i).pred in
    let flow_neg = Intlist.increase_keys delta flow.(i).succ in
    let pos = styp_consv lvl mark (map_bound_styp 0 inst Pos cons_pos) (disjoint_union eps_pos flow_pos) in
    let neg = styp_consv lvl mark (map_bound_styp 0 inst Neg cons_neg) (disjoint_union eps_neg flow_neg) in
    let v = { name; pos; neg;
              pos_match_cache = ident Pos; neg_match_cache = ident Neg } in
    let id = Vector.push tyvars v in
    assert (id = i + delta);
    (* ensure the ε-invariant is preserved *)
    Intlist.iter eps_pos (fun j () ->
      let vj = Vector.get tyvars j in
      let vjcons, vjflow = styp_unconsv lvl mark vj.neg in
      vj.neg <- styp_consv lvl mark vjcons (Intlist.add vjflow id ()));
    Intlist.iter eps_neg (fun j () ->
      let vj = Vector.get tyvars j in
      let vjcons, vjflow = styp_unconsv lvl mark vj.pos in
      vj.pos <- styp_consv lvl mark vjcons (Intlist.add vjflow id ()));
    );
  map_bound_typ 0 inst Pos body

(* NB: a similar invariant-preservation trick needed if ∀⁻ are ever merged.
   Not sure there's any need to do that, though *)

(* Open a ∀⁺ binder, extending env with flexible variables *)
let enter_poly_pos env names vars flow body =
  let env = env_cons env (Eflexible {names=SymMap.empty; vars=Vector.create ()}) in
  env, instantiate_flexible ~names env env.level env.marker vars flow body

(* Close a ∀⁺ binder, generalising flexible variables *)
let generalise env (lvl, mark) ty =
  let gen pol' index (mark', vs) { body; pol } =
    Env_marker.assert_equal mark mark';
    assert (pol = pol');
    let var, () = Intlist.as_singleton vs in
    match body with
    | Styp {cons; tyvars} when
         cons = ident pol && Intlist.is_empty tyvars ->
       { body = Bound_var {index; var}; pol }
    | _ ->
       failwith "generalise: should be a single variable" in
  let flexvars = env_flexvars env lvl mark in
  if Vector.length flexvars = 0 then ty else
  let bounds_flow = flexvars |> Vector.to_array |> Array.map (fun {pos; neg; _} ->
    let pbound, pflow = styp_unconsv lvl mark pos in
    let pbound = map_free_styp lvl mark 0 gen Pos pbound in
    let nbound, nflow = styp_unconsv lvl mark neg in
    let nbound = map_free_styp lvl mark 0 gen Neg nbound in
    (* FIXME: name generalised variables? *)
    (None, pbound, nbound), (pflow, nflow)) in
  let bounds = Array.map fst bounds_flow and flow = Array.map snd bounds_flow in
  Tpoly{names = SymMap.empty;
        bounds;
        flow = Flow_graph.make flow;
        body = map_free_typ lvl mark 0 gen Pos ty}

(* Open a ∀⁻ binder, extending env with rigid variables *)
let enter_poly_neg (env : env) names bounds flow body =
  let rigvar_level = Env_level.extend env.level in
  let rigvar_mark = Env_marker.make () in
  let inst pol v =
    let tyvars = Intlist.singleton rigvar_level (rigvar_mark, Intlist.singleton v ()) in
    { pol; body = Styp { cons = ident pol; tyvars } } in
  let vars = bounds |> Array.map (fun (name, l, u) ->
    { name;
      rig_lower = map_bound_styp 0 inst Neg l;
      rig_upper = map_bound_styp 0 inst Pos u }) in
  let body = map_bound_typ 0 inst Neg body in
  let env =
    { level = rigvar_level;
      marker = rigvar_mark;
      entry = Erigid { names; vars; flow };
      rest = Some env } in
  env, body

let enter_poly pol env names vars flow body =
  match pol with
  | Pos -> enter_poly_pos env names vars flow body
  | Neg -> enter_poly_neg env names vars flow body

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

let rec wf_env ({ level; marker=_; entry; rest } as env) =
  wf_env_entry env entry;
  match rest with
  | None -> assert (level = 0);
  | Some env' ->
     assert (level = env'.level + 1);
     wf_env env'

and wf_match_cache_entry pol env t =
  match t.body with
  | Styp {cons; tyvars} when cons = ident pol ->
     let lvl, (mark, vs) = Intlist.as_singleton tyvars in
     assert (lvl = env.level);
     Env_marker.assert_equal mark env.marker;
     let v, () = Intlist.as_singleton vs in
     assert (0 <= v && v < Vector.length (env_flexvars env env.level env.marker))
  | _ -> assert false

and wf_env_entry env = function
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
              snd (styp_unconsv env.level env.marker pos),
              snd (styp_unconsv env.level env.marker neg)) in
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
       assert (snd (styp_unconsv env.level env.marker rig_lower) = Intlist.empty);
       assert (snd (styp_unconsv env.level env.marker rig_upper) = Intlist.empty))

and wf_styp pol' env { body; pol } =
  assert (pol = pol');
  match body with
  | Bound_var _ -> assert false (* locally closed *)
  | Styp { cons; tyvars } ->
     wf_cons pol env wf_styp cons;
     wf_vset pol env tyvars

and wf_typ pol env = function
  | Tcons cons ->
     wf_cons pol env wf_typ cons
  | Tsimple s ->
     wf_styp pol env s
  | Tpoly {names; bounds; flow; body} ->
     assert (Flow_graph.length flow = Array.length bounds);
     (* toplevel references to bound variables should be in flow, not bounds *)
     bounds |> Array.iter (fun (_name, p, n) ->
       (match p.body with Bound_var _ -> assert false | _ -> ());
       (match n.body with Bound_var _ -> assert false | _ -> ()));
     let env, body = enter_poly pol env names bounds flow body in
     wf_env_entry env env.entry;
     wf_typ pol env body

and wf_vset _pol env tyvars =
  Intlist.wf tyvars;
  Intlist.iter tyvars (fun lvl (mark, vs) ->
    Intlist.wf vs;
    assert (not (Intlist.is_empty vs));
    let len =
      match env_entry_at_level env lvl mark with
      | Eflexible {vars; _} -> Vector.length vars
      | Erigid { vars; _ } -> Array.length vars
      | _ -> assert false in
    Intlist.iter vs (fun v () -> assert (0 <= v && v < len)))

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

(*
let pr_flexvar env v =
  if env.level = 1 && v < 10 then
    "'" ^ [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ" |].(v)
  else
    Printf.sprintf "'%d.%d" env.level v
*)

let pr_vset vs =
  (Intlist.to_list vs |> List.concat_map (fun (lvl, (_,vs)) ->
     Intlist.to_list vs |> List.map (fun (v,()) ->
       Printf.sprintf "#%d.%d" lvl v |> string)))

let pr_cons_tyvars pol vars cons_orig cons =
  let join = match pol with Pos -> "⊔" | Neg -> "⊓" in
  let join = blank 1 ^^ str join ^^ blank 1 in
  let pvars = separate_map join (fun v -> v) vars in
  match pol, cons_orig, vars with
  | _, _, [] -> cons
  | Pos, Bot, _
  | Neg, Top, _ -> pvars
  | _, _, _ -> parens cons ^^ join ^^ pvars

let rec pr_styp pol t =
  match t.body with
  | Bound_var { index; var } ->
     string (Printf.sprintf ".%d.%d" index var)
  | Styp { cons; tyvars } ->
     pr_cons_tyvars pol (pr_vset tyvars) cons (pr_cons pol pr_styp cons)

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

let rec pr_env { level=_; marker=_; entry; rest } =
  let doc =
    match rest with
    | None -> empty
    | Some env -> pr_env env ^^ comma ^^ break 1 in
  match entry with
  | Evals v when SymMap.is_empty v ->
     (match rest with None -> empty | Some env -> pr_env env)
  | Eflexible {vars; _} when Vector.length vars = 0 ->
     (match rest with None -> empty | Some env -> pr_env env)
  | Evals _ -> failwith "pr_env unimplemented for Evals"
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

let vsnil : vset = Intlist.empty

let make_env () = { level = Env_level.empty; marker = Env_marker.make ();
                    entry = Eflexible {vars=Vector.create ();names=SymMap.empty}; rest = None }

let bvars pol index var =
  { pol; body = Bound_var {index; var} }

let test () =
  let env = make_env () in
  let choose1_pos =
    Tpoly {names=SymMap.empty;
           bounds =[| Some "A", cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top;
                      Some "B", cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top;
                      Some "C", cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top |];
           flow=Flow_graph.of_list 3 [(0,2); (1,2)];
           body=Tsimple (cons_styp Pos vsnil (func
                 (bvars Neg 0 0)
                 (cons_styp Pos vsnil (func
                   (bvars Neg 0 1)
                   (bvars Pos 0 2)))))} in
  wf_typ Pos env choose1_pos;
  PPrint.ToChannel.pretty 1. 80 stdout
    (pr_typ Pos choose1_pos ^^ hardline);
  let nested =
    Tpoly {names=SymMap.empty;
           bounds=[| Some "A", cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top |];
           flow=Flow_graph.of_list 1 [];
           body=Tpoly {names=SymMap.empty;
                       bounds=[| Some "B", cons_styp Pos vsnil Bot, bvars Neg 1 0 |];
                       flow=Flow_graph.of_list 1 [];
                       body=Tsimple (bvars Pos 0 0)}} in
  wf_typ Pos env nested;
  PPrint.ToChannel.pretty 1. 80 stdout
    (pr_env env ^^ str " ⊢ " ^^ pr_typ Pos nested ^^ hardline);
  let body =
    match nested with
    | Tpoly {names=_; bounds; flow; body} ->
       instantiate_flexible env env.level env.marker bounds flow body
    | _ -> assert false in
  PPrint.ToChannel.pretty 1. 80 stdout
    (group (pr_env env) ^^ str " ⊢ " ^^ pr_typ Pos body ^^ hardline);
  wf_env env; wf_typ Pos env body;
  let body =
    match body with
    | Tpoly {names=_; bounds; flow; body} ->
       instantiate_flexible env env.level env.marker bounds flow body
    | _ -> assert false in
  PPrint.ToChannel.pretty 1. 80 stdout
    (group (pr_env env) ^^ str " ⊢ " ^^ pr_typ Pos body ^^ hardline);
  wf_env env; wf_typ Pos env body
  
