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
  | Eflexible of flexvar Vector.t
  (* Rigid type variables (abstract types, checked forall) *)
  | Erigid of {
      (* all fields immutable, despite array/table *)
      (* FIXME: explain why predicativity matters here *)
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
  { tyvars: vset; cons: styp cons_head; pol: polarity }

(* Sets of type variables. *)
and vset = {
  vs_free : (Env_level.t, Env_marker.t * (int, unit) Intlist.t) Intlist.t;
  vs_bound : (int, (int, unit) Intlist.t) Intlist.t
}


(* Flexible type variables.
   Maintain the ε-invariant:
   for flexible variables α, β from the same binding group,
   β ∈ α.pos.tyvars iff α ∈ β.neg.tyvars *)
and flexvar = {
    (* positive component, lower bound *)
    mutable pos : styp;
    (* negative component, upper bound *)
    mutable neg : styp;


    (* Match cache styps are either ident or a single flexible variable at the same level *)
    mutable pos_match_cache : styp cons_head;
    mutable neg_match_cache : styp cons_head;
  }

(* Rigid type variables.
   Maintain the head-invariant:
   the bounds of a rigid variable a do not mention other variables
   from the same binding group except under type constructors *)
and rigvar = {
  (* lower bound / negative component *)
  rig_lower : styp;
  (* upper bound / positive component *)
  rig_upper : styp;
}

(* General polymorphic types.  Inference may produce these after
   generalisation, but never instantiates a variable with one.
   Inference never produces Poly_neg *)
and typ =
  | Tsimple of styp
  | Tcons of typ cons_head
  (* Forall *)
  | Tpoly of (styp * styp) array * Flow_graph.t * typ

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
  | Eflexible v -> v
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

let vset_union vars1 vars2 =
  let vlist_union v1 v2 =
    Intlist.union (fun _ () () -> ()) v1 v2 in
  {
    vs_free = Intlist.union (fun _ (m1, v1) (m2, v2) ->
      Env_marker.assert_equal m1 m2;
      m1, vlist_union v1 v2) vars1.vs_free vars2.vs_free;
    vs_bound = Intlist.union (fun _ v1 v2 -> vlist_union v1 v2)
                 vars1.vs_bound vars2.vs_bound }

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

let cons_styp pol tyvars cons = { pol; tyvars; cons }
let cons_typ _pol cons = Tcons cons


(* Rewrite occurrences of the outermost bound variable *)
let rec map_bound_styp ix rw pol' { tyvars; cons; pol } =
  assert (pol = pol');
  let cons = map_head pol (map_bound_styp ix rw) cons in
  match Intlist.peel_max ix tyvars.vs_bound with
  | None -> { tyvars; cons; pol }
  | Some (vs, bound') ->
     let rest = { tyvars = { tyvars with vs_bound = bound' }; cons; pol } in
     rw vs rest

let rec map_bound_typ ix rw pol = function
  | Tsimple s -> Tsimple (map_bound_styp ix rw pol s)
  | Tcons cons -> Tcons (map_head pol (map_bound_typ ix rw) cons)
  | Tpoly (bounds, flow, body) ->
     let ix = ix + 1 in
     Tpoly (Array.map (fun (l, u) ->
                map_bound_styp ix rw pol l,
                map_bound_styp ix rw (polneg pol) u) bounds,
            flow,
            map_bound_typ ix rw pol body)

(* Rewrite occurrences of the outermost free variable *)
let rec map_free_styp lvl mark ix rw pol' { tyvars; cons; pol } =
  assert (pol = pol');
  let cons = map_head pol (map_free_styp lvl mark ix rw) cons in
  match Intlist.peel_max lvl tyvars.vs_free with
  | None -> { tyvars; cons; pol }
  | Some (vs, free') ->
     let rest = { tyvars = { tyvars with vs_free = free' }; cons; pol } in
     rw ix vs rest

(* FIXME: Tpoly_pos should have separate bounds,
   copied through here. 
   That way the rewrite function doesn't need to see poly pos flow.
   IOW: the move to canon bounds (free x cons or bound) breaks the hack that stores flow inline *)
let rec map_free_typ lvl mark ix rw pol = function
  | Tsimple s -> Tsimple (map_free_styp lvl mark ix rw pol s)
  | Tcons cons -> Tcons (map_head pol (map_free_typ lvl mark ix rw) cons)
  | Tpoly (bounds, flow, body) ->
     let ix = ix + 1 in
     Tpoly (Array.map (fun (l, u) ->
                map_free_styp lvl mark ix rw pol l,
                map_free_styp lvl mark ix rw (polneg pol) u) bounds,
            flow,
            map_free_typ lvl mark ix rw pol body)


(* FIXME: use these more *)
let styp_consv lvl mark { tyvars; cons; pol }  vs =
  let tyvars = { tyvars with vs_free = Intlist.cons_max tyvars.vs_free lvl (mark, vs) } in
  { tyvars; cons; pol }

let styp_unconsv lvl mark t =
  match Intlist.peel_max lvl t.tyvars.vs_free with
  | None -> t, Intlist.empty
  | Some ((mark', vs), rest) ->
     Env_marker.assert_equal mark mark';
     let tyvars = { t.tyvars with vs_free = rest } in
     { t with tyvars }, vs


let get_head_vars lvl mark (t : styp) =
  match Intlist.peel_max lvl t.tyvars.vs_free with
  | None -> Intlist.empty
  | Some ((mk, vs), _) ->
     Env_marker.assert_equal mk mark;
     vs

(* Open a ∀⁺ binder by instantiating its bound variables with fresh flexvars.
   Inserts variables into the current environment (no new level created) *)
let instantiate_flexible env lvl mark (vars : (styp * styp) array) (flow : Flow_graph.t) (body : typ) =
  (* The environment already contains ≥0 flexible variables, so we need to
     renumber the new ones to avoid collisions *)
  let tyvars = env_flexvars env lvl mark in
  let delta = Vector.length tyvars in
  let inst vs (t : styp) =
    let vs = Intlist.singleton lvl (mark, Intlist.increase_keys delta vs) in
    { t with tyvars = vset_union t.tyvars { vs_free = vs; vs_bound = Intlist.empty } } in
  vars |> Array.iteri (fun i (l, u) ->
    let eps_pos = get_head_vars lvl mark l in
    let eps_neg = get_head_vars lvl mark u in
    let pos = inst flow.(i).pred (map_bound_styp 0 inst Pos l) in
    let neg = inst flow.(i).succ (map_bound_styp 0 inst Neg u) in
    let v = { pos; neg;
              pos_match_cache = ident Pos; neg_match_cache = ident Neg } in
    let id = Vector.push tyvars v in
    assert (id = i + delta);
    let vs : vset = { vs_free = Intlist.singleton lvl (mark, Intlist.singleton id ());
                      vs_bound = Intlist.empty } in
    (* ensure the ε-invariant is preserved *)
    Intlist.iter eps_pos (fun j () ->
      let vj = Vector.get tyvars j in
      vj.neg <- { vj.neg with tyvars = vset_union vj.neg.tyvars vs });
    Intlist.iter eps_neg (fun j () ->
      let vj = Vector.get tyvars j in
      vj.pos <- { vj.pos with tyvars = vset_union vj.pos.tyvars vs });
    );
  map_bound_typ 0 inst Pos body

(* NB: a similar invariant-preservation trick needed if ∀⁻ are ever merged.
   Not sure there's any need to do that, though *)


(*
(* Create a single fresh variable with trivial bounds *)
let fresh_flexible env =
  let tyvars = match env with Env_cons { tyvars; _ } -> tyvars | _ -> assert false in
  let ix = Vector.length tyvars in
  let v = { env; hoisted = None; ix;
            pos = cons_styp Pos VSnil Bot;
            neg = cons_styp Neg VSnil Top } in
  let ix' = Vector.push tyvars v in
  assert (Vector.get tyvars ix == v);
  assert (ix = ix');
  v

let vset_of_flexvar v =
  VScons { env=v.env; sort = Flexible; vars = [v.ix]; rest = VSnil }

let styp_of_vset pol tyvars =
  { pol; cons = ident pol; tyvars }

let rec hoist_flexible env v =
  assert_env_prefix env v.env;
  if env == v.env then v
  else match v.hoisted with
  | None ->
     let v' = fresh_flexible env in
     v.hoisted <- Some v';
     v'
  | Some v' ->
     if env_level env < env_level v'.env then
       hoist_flexible env v'
     else
       let vh = fresh_flexible env in
       v.hoisted <- Some vh;
       vh.hoisted <- Some v';
       vh
*)


(*
(* Create flexible variables with bounds *)
let instantiate_flexible env vars =
  let tyvars = match env with Env_cons { tyvars; _ } -> tyvars | _ -> assert false in (* uglllyyyy. *)
  let nvars = Array.length vars in
  let ixs = Array.init nvars (fun _ ->
    Vector.push tyvars
      { env; ix = Vector.length tyvars; hoisted = None;
        pos = cons_styp Pos VSnil Bot;
        neg = cons_styp Neg VSnil Top }) in
  let vsets = ixs |> Array.map (fun ix ->
    VScons { env; sort = Flexible; vars = [ix]; rest = VSnil }) in
  ixs |> Array.iteri (fun i ix ->
    let v = Vector.get tyvars ix in
    let (pos, neg) = vars.(i) in
    v.pos <- is_styp (open_styp Flexible vsets 0 Pos pos);
    v.neg <- is_styp (open_styp Flexible vsets 0 Neg neg));
  vsets
*)


(* Open a ∀⁺ binder, extending env with flexible variables *)
let enter_poly_pos env vars flow body =
  let env = env_cons env (Eflexible (Vector.create ())) in
  env, instantiate_flexible env env.level env.marker vars flow body

(* Close a ∀⁺ binder, generalising flexible variables *)
let generalise env (lvl, mark) ty =
  let gen ix (mark', vs) (t : styp) =
    Env_marker.assert_equal mark mark';
    let vs = Intlist.singleton ix vs in
    { t with tyvars = vset_union t.tyvars { vs_free = Intlist.empty; vs_bound = vs } } in
  let flexvars = env_flexvars env lvl mark in
  let bounds_flow = flexvars |> Vector.to_array |> Array.map (fun {pos; neg; _} ->
    let pbound, pflow = styp_unconsv lvl mark pos in
    let pbound = map_free_styp lvl mark 0 gen Pos pbound in
    let nbound, nflow = styp_unconsv lvl mark neg in
    let nbound = map_free_styp lvl mark 0 gen Neg nbound in
    (pbound, nbound), (pflow, nflow)) in
  let bounds = Array.map fst bounds_flow and flow = Array.map snd bounds_flow in
  Tpoly(bounds,
        Flow_graph.make flow,
        map_free_typ lvl mark 0 gen Pos ty)

(* Open a ∀⁻ binder, extending env with rigid variables *)
let enter_poly_neg (env : env) bounds flow body =
  let rigvar_level = Env_level.extend env.level in
  let rigvar_mark = Env_marker.make () in
  let inst vs (t : styp) =
    let vs = Intlist.singleton rigvar_level (rigvar_mark, vs) in
    { t with tyvars = vset_union t.tyvars { vs_free = vs; vs_bound = Intlist.empty } } in
  let vars = bounds |> Array.map (fun (l, u) ->
    { rig_lower = map_bound_styp 0 inst Neg l;
      rig_upper = map_bound_styp 0 inst Pos u }) in
  let body = map_bound_typ 0 inst Neg body in
  let env =
    { level = rigvar_level;
      marker = rigvar_mark;
      entry = Erigid { vars; flow };
      rest = Some env } in
  env, body

let enter_poly pol env vars flow body =
  match pol with
  | Pos -> enter_poly_pos env vars flow body
  | Neg -> enter_poly_neg env vars flow body

(*

let enter_poly_neg env bounds flow =
  let nvars = Array.length bounds in
  let vars = Array.init nvars (fun _ ->
    { rig_lower = cons_styp Neg VSnil Bot;
      rig_upper = cons_styp Pos VSnil Top }) in
  let env_entry = Erigid { vars; flow } in
  let env = env_cons env env_entry in
  let vsets = Array.init nvars (fun i ->
    VScons { env; sort = Rigid; vars = [i]; rest = VSnil }) in
  for i = 0 to nvars - 1 do
    let (lower, upper) = bounds.(i) in
    vars.(i) <-
      { rig_lower = is_styp (open_styp Rigid vsets 0 Neg lower);
        rig_upper = is_styp (open_styp Rigid vsets 0 Pos upper) }
  done;
  env, vsets
*)


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
  let fnames = SymMap.fold (fun k _ ks -> k::ks) fields.fnamed [] |> List.rev in
  assert (fnames = List.sort compare fields.fnames);
  List.iter (wf pol env) fields.fpos;
  SymMap.iter (fun _k t -> wf pol env t) fields.fnamed

let rec wf_env ({ level; marker=_; entry; rest } as env) =
  wf_env_entry env entry;
  match rest with
  | None -> assert (level = 0);
  | Some env' ->
     assert (level = env'.level + 1);
     wf_env env'

and wf_match_cache_entry pol env t =
  assert (t.cons = ident pol);
  assert (Intlist.is_empty t.tyvars.vs_bound);
  let lvl, (mark, vs) = Intlist.as_singleton t.tyvars.vs_free in
  assert (lvl = env.level);
  Env_marker.assert_equal mark env.marker;
  let v, () = Intlist.as_singleton vs in
  assert (0 <= v && v < Vector.length (env_flexvars env env.level env.marker))

and wf_env_entry env = function
  | Evals vs ->
     SymMap.iter (fun _ typ ->  wf_typ Pos env typ) vs
  | Eflexible vars ->
     Vector.iteri vars (fun _i { pos; neg; pos_match_cache; neg_match_cache } ->
       wf_styp Pos env pos;
       wf_styp Neg env neg;
       wf_cons Pos env wf_match_cache_entry pos_match_cache;
       wf_cons Neg env wf_match_cache_entry neg_match_cache);
     (* Check the ε-invariant *)
     let head_vars =
       vars |> Vector.to_array
       |> Array.map (fun { pos; neg; _ } -> get_head_vars env.level env.marker pos, get_head_vars env.level env.marker neg) in
     head_vars |> Array.iteri (fun i (pos, neg) ->
       Intlist.iter pos (fun j () ->
         assert (Intlist.contains (snd head_vars.(j)) i));
       Intlist.iter neg (fun j () ->
         assert (Intlist.contains (fst head_vars.(j)) i)))
  | Erigid { vars; flow } ->
     assert (Flow_graph.length flow = Array.length vars);
     vars |> Array.iter (fun { rig_lower; rig_upper } ->
       wf_styp Neg env rig_lower;
       wf_styp Pos env rig_upper;
       assert (get_head_vars env.level env.marker rig_lower = Intlist.empty);
       assert (get_head_vars env.level env.marker rig_upper = Intlist.empty))

and wf_styp pol' env { tyvars; cons; pol } =
  assert (pol = pol');
  wf_cons pol env wf_styp cons;
  wf_vset pol env tyvars

and wf_typ pol env = function
  | Tcons cons ->
     wf_cons pol env wf_typ cons
  | Tsimple s ->
     wf_styp pol env s
  | Tpoly (bounds, flow, body) ->
     assert (Flow_graph.length flow = Array.length bounds);
     (* toplevel references to bound variables should be in flow, not bounds *)
     bounds |> Array.iter (fun (p, n) ->
       assert (Intlist.is_empty p.tyvars.vs_bound);
       assert (Intlist.is_empty n.tyvars.vs_bound));
     let env, body = enter_poly pol env bounds flow body in
     wf_env_entry env env.entry;
     wf_typ Pos env body

and wf_vset _pol env { vs_free; vs_bound } =
  assert (vs_bound = Intlist.empty); (* locally closed *)
  Intlist.wf vs_free;
  Intlist.iter vs_free (fun lvl (mark, vs) ->
    Intlist.wf vs;
    let len =
      match env_entry_at_level env lvl mark with
      | Eflexible fvars -> Vector.length fvars
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
  let pos_fields = fields.fpos |> List.map (pr pol) in
  let named_fields = fields.fnames |> List.map (fun k ->
    str k ^^ str ":" ^^ blank 1 ^^ pr pol (SymMap.find k fields.fnamed)) in
  let cl = match fields.fopen with `Closed -> [] | `Open -> [str "..."] in
  parens (group (nest 2 (break 0 ^^ separate (comma ^^ break 1)
                                      (pos_fields @ named_fields @ cl))))

(*
let pr_flexvar env v =
  if env.level = 1 && v < 10 then
    "'" ^ [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ" |].(v)
  else
    Printf.sprintf "'%d.%d" env.level v
*)

let pr_vset { vs_free; vs_bound } =
  (Intlist.to_list vs_free |> List.concat_map (fun (lvl, (_,vs)) ->
     Intlist.to_list vs |> List.map (fun (v,()) ->
       Printf.sprintf "#%d.%d" lvl v |> string)))
  @
  (Intlist.to_list vs_bound |> List.concat_map (fun (lvl, vs) ->
     Intlist.to_list vs |> List.map (fun (v,()) ->
       Printf.sprintf ".%d.%d" lvl v |> string)))

let pr_cons_tyvars pol vars cons_orig cons =
  let join = match pol with Pos -> "⊔" | Neg -> "⊓" in
  let join = blank 1 ^^ str join ^^ blank 1 in
  let pvars = separate_map join (fun v -> v) vars in
  match pol, cons_orig, vars with
  | _, _, [] -> cons
  | Pos, Bot, _
  | Neg, Top, _ -> pvars
  | _, _, _ -> parens cons ^^ join ^^ pvars

let rec pr_styp pol { tyvars; cons; _ } =
  pr_cons_tyvars pol (pr_vset tyvars) cons (pr_cons pol pr_styp cons)

let rec pr_typ pol = function
  | Tsimple s -> pr_styp pol s
  | Tcons cons -> pr_cons pol pr_typ cons
  | Tpoly (bounds, flow, body) ->
     str "∀" ^^ (match pol with Pos -> str "⁺" | Neg -> str "⁻") ^^ blank 1 ^^
       separate_map (str "," ^^ blank 1) (pr_bound pol) (Array.to_list bounds |> List.mapi (fun i x -> i,x)) ^^
         (Flow_graph.fold (fun acc n p ->
             acc ^^ comma ^^ break 1 ^^ str (Printf.sprintf "%d ≤ %d" n p)) flow empty) ^^
         str "." ^^ blank 1 ^^ pr_typ pol body

and pr_bound pol (ix, (lower, upper)) =
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
  | Evals _ -> failwith "pr_env unimplemented for Evals"
  | Eflexible vars ->
    Vector.fold_lefti (fun doc i v ->
      doc ^^ str (Printf.sprintf "%d" i) ^^ str ":" ^^ blank 1 ^^
        str "[" ^^ pr_styp Pos v.pos ^^ comma ^^ blank 1 ^^ pr_styp Neg v.neg ^^ str "]" ^^
          comma ^^ break 1) doc vars
  | Erigid _ -> failwith "pr_env unimplemented for Erigid"



let func a b = Func ({fpos=[a]; fnames=[]; fnamed=SymMap.empty; fopen=`Closed}, b)

let vsnil = { vs_free = Intlist.empty; vs_bound = Intlist.empty }

let make_env () = { level = Env_level.empty; marker = Env_marker.make ();
                    entry = Eflexible (Vector.create ()); rest = None }

let bvars pol lvl var =
  let vs = List.fold_left (fun vs i -> Intlist.cons_max vs i ()) Intlist.empty [var] in
  cons_styp pol { vs_free = Intlist.empty; vs_bound = Intlist.singleton lvl vs } (ident pol)

let test () =
  let env = make_env () in
  let choose1_pos =
    Tpoly ([| cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top;
              cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top;
              cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top |],
               Flow_graph.of_list 3 [(0,2); (1,2)],
               Tsimple (cons_styp Pos vsnil (func
                 (bvars Neg 0 0)
                 (cons_styp Pos vsnil (func
                   (bvars Neg 0 1)
                   (bvars Pos 0 2)))))) in
  wf_typ Pos env choose1_pos;
  PPrint.ToChannel.pretty 1. 80 stdout
    (pr_typ Pos choose1_pos ^^ hardline);

  let nested =
    Tpoly ([| cons_styp Pos vsnil Bot, cons_styp Neg vsnil Top |],
               Flow_graph.of_list 1 [],
      Tpoly ([| cons_styp Pos vsnil Bot, bvars Neg 1 0 |],
                 Flow_graph.of_list 1 [],
        Tsimple (bvars Pos 0 0))) in
  wf_typ Pos env nested;
  PPrint.ToChannel.pretty 1. 80 stdout
    (pr_env env ^^ str " ⊢ " ^^ pr_typ Pos nested ^^ hardline);
  let body =
    match nested with
    | Tpoly (bounds, flow, body) ->
       instantiate_flexible env env.level env.marker bounds flow body
    | _ -> assert false in
  PPrint.ToChannel.pretty 1. 80 stdout
    (group (pr_env env) ^^ str " ⊢ " ^^ pr_typ Pos body ^^ hardline);
  wf_env env; wf_typ Pos env body;
  let body =
    match body with
    | Tpoly (bounds, flow, body) ->
       instantiate_flexible env env.level env.marker bounds flow body
    | _ -> assert false in
  PPrint.ToChannel.pretty 1. 80 stdout
    (group (pr_env env) ^^ str " ⊢ " ^^ pr_typ Pos body ^^ hardline);
  wf_env env; wf_typ Pos env body
  
