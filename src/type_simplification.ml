open Typedefs

(*
I can see three basic ways of doing generalisation / simplification.

 1. Remove meets/joins, then apply as many GC-type transformations as you can
    without reintroducing them. (See Pass I, II, III below)

 2. Remove meets/joins and fold/remove monopolar variables until all flow is - → +
    (The folding may introduce new meets and joins, so continue until fixpoint)
    This is more or less MLsub1 canonisation + DFA conversion.
    Some head expansion occurs, but I think not much?
    Some types will be better simplified this way.

 3. Do #2, but also reintroduce sharing (e.g. by hashconsing, or better, Hopcroft's) and
    optimise type variables by sharing bicliques. This is roughly MLsub1 minimisation.
    There is an alternative way to optimise type variables by partition refinement,
    which is cheaper and easier than finding bicliques.

So far, this is (1). Doing (2) might be interesting, but it's pretty fiddly.
I think the new design introduces far fewer variables, so #3 should not be needed.
(This is hopefully even more true with gen-after-APP).

There are a couple of optimisations not done yet that don't quite fit into canonisation/gc:

  - If a variable is constrained as A ≤ α ≤ B, where B ≤ A, then delete it.

  - Flow can be optimised by (a) removing SCCs (see above) and (b) transitive reduction.
    (a) is particularly important, since some bits of GC may diverge on flow loops.

Recursive types are badly handled so far. In particular, type variables that mention
themselves in their own bound should not be removed, even if monopolar. I think this
can be computed during the polarity DFS, by locating backedges. (weak guardedness)
*)

(* Canonisation.
   Bring a type with flexvars into 1BV form:
     the type and the constructed part of each flexvar bound
     never contains a meet/join at this level.
     (either a single var at this level with trival ctor, or none).
   Since this does a traversal, this could be done in the same pass as
   polarity computation for GC.
   FIXME: would be better to do this, because this current wastes
          time redundantly canonising useless variables.
*)
let remove_joins env (lvl, mark) ty =
  wf_typ Pos env ty;
  (* FIXME: this is a poor way to key this table.
     Hashing styps isn't very reliable, because tuple_fields are not canonical
     (this only causes a possible loss of sharing, though) *)
  let canon_table : (polarity * styp * (int, unit) Intlist.t, styp) Hashtbl.t = Hashtbl.create 10 in
  let flexvars = env_flexvars env lvl mark in

  (* FIXME: this can probably determine recursive reachability, for rectypes *)

  let rec canon pol ty =
    map_free_styp lvl mark 0 canon_var pol ty

  and canon_var pol _ix (mark', vs) (rest : styp) =
    Env_marker.assert_equal mark mark';
    (* map_free_styp should never call us with an empty vs *)
    assert (not (Intlist.is_empty vs));
    match rest, vs with
    | { body = Styp {cons; tyvars}; pol }, vs when
           cons = ident pol &&
           Intlist.is_empty tyvars &&
           Intlist.is_singleton vs ->
       (* 1BV because only one var at this level *)
       cons_styp pol (Intlist.singleton lvl (mark', vs)) (ident pol)
    | _, vs ->
       (* Otherwise, need to introduce a new flexvar to enforce 1BV *)
       let key = (pol, rest, vs) in
       match Hashtbl.find canon_table key with
       | t' -> t'
       | exception Not_found ->
          let (n, p) = Types.fresh_flow env (lvl, mark) in
          let t = styp_consv lvl mark rest vs in
          let nofail = function [] -> () | _ -> assert false in
          let repl =
            match pol with
            | Pos -> Types.subtype_styp env (Hashtbl.create 1) t n |> nofail; p
            | Neg -> Types.subtype_styp env (Hashtbl.create 1) p t |> nofail; n in
          Hashtbl.add canon_table key repl;
          repl in
  (* iterate only over original vars, not any new ones *)
  for i = 0 to Vector.length flexvars - 1 do
    let v = Vector.get flexvars i in
    let pcons, pvar = styp_unconsv lvl mark v.pos in
    let pcons = canon Pos pcons in
    v.pos <- styp_consv lvl mark pcons pvar;
    v.pos_match_cache <- ident Pos;
    let ncons, nvar = styp_unconsv lvl mark v.neg in
    let ncons = canon Neg ncons in
    v.neg <- styp_consv lvl mark ncons nvar;
    v.neg_match_cache <- ident Neg
  done;
  let ty = map_free_typ lvl mark 0 canon_var Pos ty in
  wf_env_entry env (env_entry_at_level env lvl mark);
  wf_typ Pos env ty;
  ty


type gc_var_side =
  { mutable weak : bool;
    mutable strong : bool;
    mutable cons : styp;
    mutable flow : (int, unit) Intlist.t }

type replacement =
  | Unknown
  | Deleted
  | Link of int
  | Keep of Env_marker.t * int
  | SubstPre of styp            (* in old env *)
  | SubstPost of styp           (* in new env *)

type gc_var =
  { vneg : gc_var_side;
    vpos : gc_var_side;
    mutable replacement : replacement }

let var_side pol { vneg; vpos; _ } =
  match pol with Neg -> vneg | Pos -> vpos

(* FIXME:
   Some of these optimisations assume coherence.
   (More precisely: can make incoherent envs coherent)
   Are envs assumed coherent? *)
(* FIXME:
   this probably goes wrong when there are flow cycles.
   Detect/remove these first? May also be good to run transitive reduction *)
(* FIXME:
   tricky example to try when parser is better:
     α ≤ C
     γ ≤ α ≤ β ≤ D ⊢ α → (β × γ)
   α should be expanded to C ⊓ β, even in the upper bound of +-reachable γ *)
let garbage_collect env (lvl, mark) ty =
  (* let orig_ty = ty in *)
  wf_typ Pos env ty;
  let orig_flexvars = env_flexvars env lvl mark in
  let vars = Vector.to_array orig_flexvars |> Array.map (fun { pos; neg; _ } ->
    let pos_cons, pos_flow = styp_unconsv lvl mark pos in
    let neg_cons, neg_flow = styp_unconsv lvl mark neg in
    { vpos = { weak = false; strong = false; cons = pos_cons; flow = pos_flow };
      vneg = { weak = false; strong = false; cons = neg_cons; flow = neg_flow };
      replacement = Unknown }) in

  let mark_deleted v =
    v.vneg.cons <- cons_styp Neg vsnil (ident Neg);
    v.vneg.flow <- Intlist.empty;
    v.vpos.cons <- cons_styp Pos vsnil (ident Pos);
    v.vpos.flow <- Intlist.empty;
    v.replacement <- Deleted in

  (* FIXME rectypes.
     
     Is it enough to mark back-edges in the DFS that computes polarities?
     Every cycle must pass through a back-edge. 
     Slightly tricky to combine this with the edge-shortening (variable removal)
     which occurs later.
   *)

  (* First, compute polarities *)
  let rec visit_bound pol v =
    let v = vars.(v) in
    let vs = var_side pol v in
    if vs.weak then () else begin
      vs.weak <- true;
      visit_styp pol vs.cons;
      Intlist.iter vs.flow (fun v' () -> visit_bound pol v')
    end
  and visit_styp pol t =
    assert (pol = t.pol);
    ignore (map_free_styp lvl mark 0 visit_vars_strong pol t)
  and visit_vars_strong pol _ix (mark', vs) (rest : styp) =
    Env_marker.assert_equal mark mark';
    assert (is_trivial pol rest); (* Should be 1BV form already *)
    Intlist.iter vs (fun v () ->
      (var_side pol vars.(v)).strong <- true;
      visit_bound pol v);
    (* unused. Maybe I need an iter_free_styp... *)
    cons_styp pol vsnil (ident pol) in
  ignore (map_free_typ lvl mark 0 visit_vars_strong Pos ty);

  (* FIXME: write tests that hit each of these cases *)

  (* Pass I. Remove totally useless stuff: unreachable bounds and unreachable vars. *)
  vars |> Array.iter (fun v ->
    if not v.vneg.weak then v.vneg.cons <- cons_styp Neg vsnil (ident Neg);
    if not v.vpos.weak then v.vpos.cons <- cons_styp Pos vsnil (ident Pos);
    (* FIXME: bug here.
       Suppose β ≤ α ⊓ γ ⊢ γ.
       γ strong+, β weak+, α unreachable.
       α should be deleted, but we need to remove flow edges from β to match.
       Try and hit this with a test?
     *)
    if not v.vneg.weak && not v.vpos.weak then mark_deleted v);
  (* Now:
     Every variable appearing in a bound is strongly reachable.
     Every variable with nonzero flow is at least weakly reachable. *)

  let remove_all_flow vi =
    let v = vars.(vi) in
    Intlist.iter v.vneg.flow (fun v' () ->
      let v' = vars.(v').vpos in
      v'.flow <- Intlist.union (fun _ () () -> ()) v'.flow v.vpos.flow;
      v'.flow <- Intlist.remove v'.flow (Intlist.singleton vi []));
    Intlist.iter v.vpos.flow (fun v' () ->
      let v' = vars.(v').vneg in
      v'.flow <- Intlist.union (fun _ () () -> ()) v'.flow v.vneg.flow;
      v'.flow <- Intlist.remove v'.flow (Intlist.singleton vi []));
    v.vneg.flow <- Intlist.empty;
    v.vpos.flow <- Intlist.empty in
    


  (* Pass IIa. Delete variables not strongly reachable with trivial cons bounds *)
  vars |> Array.iteri (fun vi v ->
    if not v.vneg.strong && not v.vpos.strong &&
         is_trivial Neg v.vneg.cons && is_trivial Pos v.vpos.cons then begin
      remove_all_flow vi;
      mark_deleted v;           (* FIXME remove *)
    end);

  (* Pass IIIa. Merge variables with a unique other variable *)
  vars |> Array.iteri (fun vi v ->
    if not v.vpos.strong &&
         is_trivial Neg v.vneg.cons &&
         is_trivial Pos v.vpos.cons &&
         Intlist.is_singleton v.vneg.flow then begin
      let (v', ()) = Intlist.as_singleton v.vneg.flow in
      remove_all_flow vi;
      (* may have made v' strongly reachable. (Breaks symmetry, constructs bipolar vars) *)
      if v.vneg.strong then vars.(v').vneg.strong <- true;
      v.replacement <- Link v';
    end
    else if not v.vneg.strong &&
         is_trivial Neg v.vneg.cons &&
         is_trivial Pos v.vpos.cons &&
         Intlist.is_singleton v.vpos.flow then begin
      let (v', ()) = Intlist.as_singleton v.vpos.flow in
      remove_all_flow vi;
      (* may have made v' strongly reachable. (Breaks symmetry, constructs bipolar vars) *)
      if v.vpos.strong then vars.(v').vpos.strong <- true;
      v.replacement <- Link v';
    end);

  (* Pass IIIb. Remove variables reachable with only one polarity, and no flow *)
  vars |> Array.iter (fun v ->
    if v.replacement = Unknown then begin
      if not v.vpos.strong && Intlist.is_empty v.vneg.flow && Intlist.is_empty v.vpos.flow then begin
        v.replacement <- SubstPre v.vneg.cons
      end
      else if not v.vneg.strong && Intlist.is_empty v.vneg.flow && Intlist.is_empty v.vpos.flow then begin
        v.replacement <- SubstPre v.vpos.cons
      end
   end);

  let new_env_marker = Env_marker.make () in
  let num_new_vars = ref 0 in
  vars |> Array.iter (fun v ->
    if v.replacement = Unknown then begin
      let id = !num_new_vars in
      incr num_new_vars;
      v.replacement <- Keep (new_env_marker, id)
    end);

  let rec replace_var pol v =
    let v = vars.(v) in
    match v.replacement with
    | Unknown -> assert false
    | Deleted -> assert false
    | Link v' ->
       replace_var pol v' (* could path compress... *)
    | Keep (mark, v) ->
       cons_styp pol (Types.vset_of_flexvar (lvl, mark) v) (ident pol)
    | SubstPost t -> t
    | SubstPre t ->
       let t = replace_styp pol t in
       v.replacement <- SubstPost t;
       t
  and replace_styp pol t =
    map_free_styp lvl mark 0 replace_vars pol t
  and replace_vars pol _ix (mark', vs) (rest : styp) =
    Env_marker.assert_equal mark mark';
    (* no joins: if we have vs, then rest should be trivial *)
    assert (Intlist.is_singleton vs);
    assert (is_trivial pol rest);
    let (v, ()) = Intlist.as_singleton vs in
    replace_var rest.pol v in

  let new_flexvars : flexvar Vector.t =
    Array.init !num_new_vars (fun _ ->
      { name = None;
        pos = cons_styp Pos vsnil (ident Pos);
        neg = cons_styp Neg vsnil (ident Neg);
        pos_match_cache = ident Pos;
        neg_match_cache = ident Neg })
    |> Vector.of_array in

  let convert_flow flow =
    flow
    |> Intlist.to_list
    |> List.map (fun (v,()) -> match vars.(v).replacement with Keep (_,ix) -> ix | _ -> assert false)
    |> List.fold_left (fun vs v -> Intlist.union (fun _ () () -> ()) vs (Intlist.singleton v ())) Intlist.empty in
  vars |> Array.iter (fun v ->
    match v.replacement with
    | Keep (_, ix) ->
       let v' = Vector.get new_flexvars ix in
       v'.pos <- styp_consv lvl new_env_marker (replace_styp Pos v.vpos.cons) (convert_flow v.vpos.flow);
       v'.neg <- styp_consv lvl new_env_marker (replace_styp Neg v.vneg.cons) (convert_flow v.vneg.flow); 
    | _ -> ());
  let ty = map_free_typ lvl mark 0 replace_vars Pos ty in

  let env' =
    let { marker = mark'; rest; _ } = env in
    Env_marker.assert_equal mark mark';
    { level = lvl;
      marker = new_env_marker;
      entry = Eflexible {vars=new_flexvars;names=Tuple_fields.SymMap.empty};
      rest } in
  wf_env_entry env' (env_entry_at_level env' lvl new_env_marker);
  wf_typ Pos env' ty;
  env', ty
  

    (*


  (* Pass II. Substitute away variables not strongly reachable.
     This removes variables by transitivity.
     Since these are not strongly reachable, they do not appear in bounds. *)
  vars |> Array.iteri (fun vi v ->
    if not v.vneg.strong && not v.vpos.strong then begin
      (* This variable appears only in other variable's flow. Remove it. *)
      Intlist.iter v.vneg.flow (fun v' () ->
        let v' = vars.(v').vpos in
        v'.cons <- Types.join Pos v'.cons v.vpos.cons;
        v'.flow <- Intlist.union (fun _ () () -> ()) v'.flow v.vpos.flow;
        v'.flow <- Intlist.remove v'.flow (Intlist.singleton vi []));
      Intlist.iter v.vpos.flow (fun v' () ->
        let v' = vars.(v').vneg in
        v'.cons <- Types.join Neg v'.cons v.vneg.cons;
        v'.flow <- Intlist.union (fun _ () () -> ()) v'.flow v.vneg.flow;
        v'.flow <- Intlist.remove v'.flow (Intlist.singleton vi []));
      mark_deleted v;
    end);

  (* Now:
     Every variable appearing in a bound is strongly reachable.
     Every variable with nonzero flow or nonzero bound is strongly reachable *)

  (* Pass III. Remove all flow edges which are not - -> +??? 
     No, don't. This risks duplicating, without deleting a var *)

  (* Pass III. Remove all monopolar variables with flow only to the same polarity.
     These may show up in bounds and in the result type, so actual subst needed *)
  vars |> Array.iter (fun v ->
    if v.vneg.strong && not v.vpos.strong &&
         Intlist.to_list v.vneg.flow |> List.for_all (fun (v',()) ->
           not vars.(v').vpos.strong) then
      v.vneg.should_subst <- true;
    if v.vpos.strong && not v.vneg.strong &&
         Intlist.to_list v.vpos.flow |> List.for_all (fun (v',()) ->
           not vars.(v').vneg.strong) then
      v.vpos.should_subst <- true);

  let rec replacement pol vix =
    let v = var_side pol vars.(vix) in
    assert (v.strong); assert (v.should_subst);
    match v.subst_computed with
    | Some t -> t
    | None ->
       let cons = map_free_styp lvl mark 0 substitute_vars pol v.cons in
       let ty = substitute_vars 0 (mark, v.flow) cons in
       v.subst_computed <- Some ty;
       mark_deleted vars.(vix);
       ty
  and substitute_vars _ix (mark', vs) (rest : styp) =
    let pol = rest.pol in
    Env_marker.assert_equal mark mark';
    let keep = Intlist.filter (fun v () -> not ((var_side pol vars.(v)).should_subst)) vs in
    let subst = Intlist.filter (fun v () -> (var_side pol vars.(v)).should_subst) vs in
    List.fold_left (fun ty (v,()) ->
      Types.join pol ty (replacement pol v)) (styp_consv lvl mark rest keep) (Intlist.to_list subst) in
  vars |> Array.iter (fun v ->
    if not v.vpos.should_subst && not v.vneg.should_subst then begin
      let pos_cons = map_free_styp lvl mark 0 substitute_vars Pos v.vpos.cons in
      let pos_subst = substitute_vars 0 (mark, v.vpos.flow) pos_cons in
      let (pos_newcons, pos_newflow) = styp_unconsv lvl mark pos_subst in
      v.vpos.cons <- pos_newcons;
      v.vpos.flow <- pos_newflow;
      let neg_cons = map_free_styp lvl mark 0 substitute_vars Neg v.vneg.cons in
      let neg_subst = substitute_vars 0 (mark, v.vneg.flow) neg_cons in
      let (neg_newcons, neg_newflow) = styp_unconsv lvl mark neg_subst in
      v.vneg.cons <- neg_newcons;
      v.vneg.flow <- neg_newflow;
    end);
  let ty = map_free_typ lvl mark 0 substitute_vars Pos ty in
  vars |> Array.iter (fun v ->
    if v.vneg.should_subst then assert (v.vneg.subst_computed <> None && v.vdelete);
    if v.vpos.should_subst then assert (v.vpos.subst_computed <> None && v.vdelete));
  (* Now:
     Every variable is strongly reachable and has at least one - -> + flow *)

  

  (* FIXME: consider changing the env mark *)
  let new_env_marker = mark in
  let new_flexvars =
    vars |>
    Array.map (fun v ->
      { pos = styp_consv lvl mark v.vpos.cons v.vpos.flow;
        neg = styp_consv lvl mark v.vneg.cons v.vneg.flow;
        pos_match_cache = ident Pos;
        neg_match_cache = ident Neg })
    |> Vector.of_array in
  let env' =
    let { marker = mark'; rest; _ } = env in
    Env_marker.assert_equal mark mark';
    { level = lvl;
      marker = new_env_marker;
      entry = Eflexible new_flexvars;
      rest } in
  wf_env_entry env' (env_entry_at_level env' lvl new_env_marker);
  wf_typ Pos env' ty;
  env', ty
*)


(*
Previous attempt at GC.


type reachability =
  { mutable pos_reachable : bool;
    mutable neg_reachable : bool }
let fresh_reachability () =
  { pos_reachable = false;
    neg_reachable = false }
let is_reachable pol r =
  match pol with
  | Pos -> r.pos_reachable
  | Neg -> r.neg_reachable
let set_reachable pol r =
  match pol with
  | Pos -> r.pos_reachable <- true
  | Neg -> r.neg_reachable <- true

type gc_outcome =
  | Unprocessed
  | Zap of polarity * styp
  | Keeping of { id : int }
  | Kept of { id : int; pos : styp; neg : styp }

let garbage_collect' env (lvl, mark) ty =
  let orig_ty = ty in
  wf_typ Pos env ty;
  let flexvars = env_flexvars env lvl mark in
  let nvars = Vector.length flexvars in
  let reachable = Vector.create () in
  for i = 0 to Vector.length flexvars - 1 do
    let i' = Vector.push reachable (fresh_reachability ()) in
    assert (i = i');
  done;

  (* FIXME: this can probably determine recursive reachability, for rectypes *)
  let rec visit_bound pol v =
    let r = Vector.get reachable v in
    let v = Vector.get flexvars v in
    if is_reachable pol r then () else begin
      set_reachable pol r;
      let bound = match pol with Pos -> v.pos | Neg -> v.neg in
      let consb, varb = styp_unconsv lvl mark bound in
      let consb', varb = Types.flex_closure pol env lvl flexvars consb Intlist.empty varb in
      let _ = map_free_styp lvl mark 0 canon pol consb' in
      let _bound = styp_consv lvl mark consb varb in
      (* FIXME: kinda ugly invalidation here. *)
      v.pos_match_cache <- ident Pos;
      v.neg_match_cache <- ident Neg; (*
      match pol with
      | Pos -> v.pos <- bound
      | Neg -> v.neg <- bound *)
    end

  and visit_bounds pol vs =
    Intlist.iter vs (fun v' () -> visit_bound pol v')

  and canon _ix (mark', vs) (rest : styp) =
    Env_marker.assert_equal mark mark';
    visit_bounds rest.pol vs;
    styp_consv lvl mark rest vs in
  let ty = map_free_typ lvl mark 0 canon Pos ty in

  let replaceable pol v =
    not (is_reachable (polneg pol) (Vector.get reachable v)) in

  let replacement_cache = Array.make nvars Unprocessed in
  let num_new_vars = ref 0 in
  let new_env_marker = Env_marker.make () in
  let kept_var_worklist = ref [] in

  (* FIXME: Probably diverges on strongly-connected flow edges and recursive types *)
  let rec replacement pol vix =
    assert (replaceable pol vix);
    match replacement_cache.(vix) with
    | Keeping _ | Kept _ ->
       assert false
    | Zap (pol', t) ->
       assert (pol = pol'); t
    | Unprocessed ->
      let v = Vector.get flexvars vix in
      let bound = match pol with Pos -> v.pos | Neg -> v.neg in
      let consb, varb = styp_unconsv lvl mark bound in
      let consb = map_free_styp lvl mark 0 replace_all pol consb in
      let t = replace_all 0 (mark, varb) consb in
      replacement_cache.(vix) <- Zap (pol, t);
      t

  and keep_var v =
    assert (not (replaceable Pos v) && not (replaceable Neg v));
    let id =
      match replacement_cache.(v) with
      | Keeping { id } | Kept { id; _ } -> id
      | Zap _ -> assert false
      | Unprocessed ->
          let id = !num_new_vars in
          incr num_new_vars;
          replacement_cache.(v) <- Keeping { id };
          kept_var_worklist := v :: !kept_var_worklist;
          id in
    Types.vset_of_flexvar (lvl, new_env_marker) id

  and replace_all _ix (mark', vs) (rest : styp) =
    Env_marker.assert_equal mark mark';
    let pol = rest.pol in
    let vnonreplaceable = Intlist.filter (fun v' () -> not (replaceable pol v')) vs in
    let vreplaceable = Intlist.filter (fun v' () -> replaceable pol v') vs in
    (* The nonreplaceable variables will now show up at polarity pol. Mark this. *)
    let newvs = Intlist.to_list vnonreplaceable |> List.map (fun (v', ()) ->
      (* FIXME: the order of events is pretty dubious here. Is this correct? *)
      set_reachable pol (Vector.get reachable v');
      keep_var v') in
    let newvs = List.fold_left vset_union vsnil newvs in
    let t = Types.join pol rest (cons_styp pol newvs (ident pol)) in
    let t = Intlist.to_list vreplaceable |> List.fold_left (fun t (v', ()) ->
      Types.join pol t (replacement pol v')) t in
    t in

  let ty = map_free_typ lvl mark 0 replace_all Pos ty in

  PPrint.ToChannel.pretty 1. 80 stdout PPrint.((group @@ group (string "*" ^^ Typedefs.pr_env env) ^^ break 1 ^^ group (utf8string "⊢" ^^ break 1 ^^ (Typedefs.pr_typ Pos orig_ty)) ^^ hardline));
  for i = 0 to nvars - 1 do
    match replacement_cache.(i) with
    | Keeping _ -> Printf.printf "%d keeping\n%!" i
    | Kept _ -> Printf.printf "%d kept\n%!" i
    | Unprocessed -> Printf.printf "%d u\n%!" i
    | Zap (p,_) -> Printf.printf "%d z%c\n%!" i (match p with Pos -> '+' | Neg -> '-')
  done;

  while !kept_var_worklist <> [] do
    let v = List.hd !kept_var_worklist in
    kept_var_worklist := List.tl !kept_var_worklist;
    let fv = Vector.get flexvars v in
    let pos = map_free_styp lvl mark 0 replace_all Pos fv.pos in
    let neg = map_free_styp lvl mark 0 replace_all Neg fv.neg in
    match replacement_cache.(v) with
    | Keeping { id } -> replacement_cache.(v) <- Kept { id; pos; neg }
    | _ -> assert false
  done;

  let new_flex_vars : flexvar Vector.t = Vector.create () in
  for i = 0 to !num_new_vars - 1 do
    let i' = Vector.push new_flex_vars
               { pos = cons_styp Pos vsnil (ident Pos);
                 neg = cons_styp Neg vsnil (ident Neg);
                 pos_match_cache = ident Pos;
                 neg_match_cache = ident Neg } in
    assert (i = i');
  done;
  for i = 0 to nvars - 1 do
    match replacement_cache.(i) with
    | Kept {id; pos; neg} ->
       let fv = Vector.get new_flex_vars id in
       fv.pos <- pos;
       fv.neg <- neg;
    | Keeping _ -> assert false
    | _ -> ()
  done;

  PPrint.ToChannel.pretty 1. 80 stdout PPrint.((group @@ group (string "*" ^^ Typedefs.pr_env env) ^^ break 1 ^^ group (utf8string "⊢" ^^ break 1 ^^ (Typedefs.pr_typ Pos orig_ty)) ^^ hardline));


  let env' =
    let { marker = mark'; rest; _ } = env in
    Env_marker.assert_equal mark mark';
    { level = lvl;
      marker = new_env_marker;
      entry = Eflexible new_flex_vars;
      rest } in

  PPrint.ToChannel.pretty 1. 80 stdout PPrint.((group @@ group (string "*" ^^ Typedefs.pr_env env') ^^ break 1 ^^ group (utf8string "⊢" ^^ break 1 ^^ (Typedefs.pr_typ Pos ty)) ^^ hardline));


  wf_env_entry env' (env_entry_at_level env' lvl new_env_marker);
  wf_typ Pos env' ty;
  env', ty


(* Canonisation.
   Bring a type with flexvars into 1BV form:
     the type and the constructed part of each flexvar bound
     never contains a meet/join at this level.
     (either a single var at this level with trival ctor, or none) *)
let canonise env (lvl, mark) ty =
  wf_typ Pos env ty;
  (* FIXME: this is a poor way to key this table.
     Hashing styps isn't very reliable, because tuple_fields are not canonical
     (this only causes a possible loss of sharing, though) *)
  let canon_table : (polarity * styp * (int, unit) Intlist.t, styp) Hashtbl.t = Hashtbl.create 10 in
  let flexvars = env_flexvars env lvl mark in
  let reachable = Vector.create () in
  for i = 0 to Vector.length flexvars - 1 do
    let i' = Vector.push reachable (fresh_reachability ()) in
    assert (i = i');
  done;

  (* FIXME: this can probably determine recursive reachability, for rectypes *)
  let rec visit_bound pol v =
    let r = Vector.get reachable v in
    let v = Vector.get flexvars v in
    if is_reachable pol r then () else begin
      set_reachable pol r;
      let bound = match pol with Pos -> v.pos | Neg -> v.neg in
      let consb, varb = styp_unconsv lvl mark bound in
      visit_bounds pol varb;
      let consb = map_free_styp lvl mark 0 canon pol consb in
      let bound = styp_consv lvl mark consb varb in
      (* FIXME: kinda ugly invalidation here. *)
      v.pos_match_cache <- ident Pos;
      v.neg_match_cache <- ident Neg;
      match pol with
      | Pos -> v.pos <- bound
      | Neg -> v.neg <- bound
    end

  and visit_bounds pol vs =
    Intlist.iter vs (fun v' () -> visit_bound pol v')

  and canon _ix (mark', vs) (rest : styp) =
    Env_marker.assert_equal mark mark';
    visit_bounds rest.pol vs;
    match rest, vs with
    | rest, vs when Intlist.is_empty vs ->
       (* 1BV because no vars at this level *)
       rest
    | { cons; tyvars; pol }, vs when
           cons = ident pol &&
           Intlist.is_empty tyvars.vs_free &&
           Intlist.length vs = 1 ->
       (* 1BV because only one var at this level *)
       (* FIXME: figure out whether tyvars.vs_bound must be empty. True by 1BV assumption? *)
       cons_styp pol { tyvars with vs_free = (Intlist.singleton lvl (mark', vs)) } (ident pol)
    | { pol; _ }, vs ->
       (* Otherwise, need to introduce a new flexvar to enforce 1BV *)
       let key = (pol, rest, vs) in
       match Hashtbl.find canon_table key with
       | t' -> t'
       | exception Not_found ->
          let (n, p) = Types.fresh_flow env (lvl, mark) in
          let () =
            let r = fresh_reachability () in
            set_reachable pol r; (* bounds already 1BV *)
            let ix = Vector.push reachable r in
            assert (ix = Vector.length flexvars - 1) in
          let t = styp_consv lvl mark rest vs in
          let nofail = function [] -> () | _ -> assert false in
          let repl =
            match pol with
            | Pos -> Types.subtype_styp env t n |> nofail; p
            | Neg -> Types.subtype_styp env p t |> nofail; n in
          Hashtbl.add canon_table key repl;
          repl in
  let ty = map_free_typ lvl mark 0 canon Pos ty in
  wf_env_entry env (env_entry_at_level env lvl mark);
  wf_typ Pos env ty;
  ty, reachable

*)

(*
(* Reachable parts of ty assumed to be in 1BV form.
   Replace mono-reachable flex vars with their unique bound, where possible *)
let zap env (lvl, mark) reachable ty =
  wf_typ Pos env ty;
  let flexvars = env_flexvars env lvl mark in
  let nvars = Vector.length flexvars in
  assert (Array.length reachable = nvars);
  let pos_replacements = Array.make nvars None in
  let neg_replacements = Array.make nvars None in
  let next_new_var = ref 0 in
  
  let rec allocate_var pol v =


  let rec var_replacement pol v : styp =
    assert (is_reachable pol reachable.(v));
    let must_keep = is_reachable (polneg pol) reachable.(v) in
    let fv = Vector.get flexvars v in
    let bound = match pol with Pos -> fv.pos | Neg -> fv.neg in
    let consb, varb = styp_unconsv lvl mark bound in
    let var_replacements =
      (* FIXME: diverges on flow cycles *)
      Intlist.to_list varb
      |> List.map (fun (v', ()) -> var_replacement pol v')
      |> List.filter (fun s -> not (bound_is_trivial pol s)) in
    let replacement =
      match var_replacements with
      | [] ->
         (* replace with zapped consb *)
         zapconsb
      | [v] when bound_is_trivial pol consb ->
         v
      | _ ->
         (* keep the variable to ensure canonicity, even though monopolar *)
         keep

    if is_reachable (polneg pol) reachable.(v) then
      (* keep this variable *)
      asdf
    else
       
    asdf

*)

(*


open Typedefs


(*

Simplification algorithm.

1. Traversal.
   Traverse but do not construct the canonised type.
     follow : polarity -> fvars -> fvars * styp
   canonises a subset of the flexvars and computes its successor
     follow pol vs = (ε-closure vs, join of bounds of ε-closure)
   This is roughly the powerset construction making a DFA.
   Perform a DFS on these powersets (using a hashtable for visit marks).

   At each DFS node, mark the members of the fvar set.
   At each DFS node, refine the partition R by the fvar set.

   Result:
     Set of positively, negatively reachable variables
     Coarsest partitions R⁺, R⁻ with α Rπ β when α,β co-occur at polarity π.

2. Compute merge classes and their reachability.
   Assign each variable to the bigger of its R⁻-class or R⁺-class.
   Break ties towards, say, -.
   Compute positive, negative reachability marks for each class.
   In a R⁻-class, all variables should agree on (-)-reachability.
   An R⁻ class is (+)-reachable if any of its members are.

   Result:
     Map from old fvars to merge classes
     (-)/(+)-reachability of each merge class

3. Compute replacements and bounds for each merge class.
   If both (+) and (-)-reachable, replacement is a fresh variable.
   If only (+) or (-)-reachable, replacement is join of bounds.
   NB: recursion may require a fresh variable, to maintain finiteness.
   If not reachable, no replacement is needed.

4. Compute new type and new bounds by making replacements.


 *)



(* FIXME: I think this GC algorithm never causes head-expansion, but check *)
(* Performs GC on the flexible variables at the end of env.
   Used when closing an Egen. Is there any other time to use it?
   Is it ever useful to GC more deeply than this? Wouldn't be hard if so. *)
let garbage_collect env pol ty =
  wf_env env;
  wf_styp pol env ty;
  (* Phase I. Mark live variables. Note separate Pos and Neg marks *)
  let old_vars = Vector.to_array (env_flexvars env) in
  let pos_mark = Array.make (Array.length old_vars) false in
  let neg_mark = Array.make (Array.length old_vars) false in
  let is_marked pol v =
    assert (v.env == env);
    match pol with Pos -> pos_mark.(v.ix) | Neg -> neg_mark.(v.ix) in
  let set_mark pol v =
    assert (v.env == env);
    match pol with Pos -> pos_mark.(v.ix) <- true | Neg -> neg_mark.(v.ix) <- true in
  let rec mark_var pol v =
    assert_env_prefix v.env env;
    if v.env == env && not (is_marked pol v) then begin
      set_mark pol v;
      let bound = match pol with Pos -> v.pos | Neg -> v.neg in
      mark_styp pol bound
    end
  and mark_styp pol t =
    wf_styp pol env t;
    let ({ cons; _ }, vs) = styp_uncons env Flexible t in
    vs |> List.iter (fun i -> mark_var pol (env_flexvar env i));
    let _ : unit cons_head = map_head pol mark_styp cons in
    () in
  mark_styp pol ty;
  (* Phase II. Trim the list of variables.
     Only keep variables that are marked both positively and negatively. *)
  Vector.clear (env_flexvars env);
  let kept_vars = Array.map2 (fun p n -> if p && n then Some (fresh_flexible env) else None)
                    pos_mark neg_mark in
  let rewrite_pos = Array.make (Array.length old_vars) None in
  let rewrite_neg = Array.make (Array.length old_vars) None in
  kept_vars |> Array.iteri (fun i k ->
    match k with
    | Some v ->
      let v = vset_of_flexvar v in
      rewrite_pos.(i) <- Some (cons_styp Pos v (ident Pos));
      rewrite_neg.(i) <- Some (cons_styp Neg v (ident Neg));
    | None -> ());

  let currently_rewriting = Array.make (Array.length old_vars) false in
  let rec rewrite_var pol i =
    let rw = match pol with Neg -> rewrite_neg | Pos -> rewrite_pos in
    match rw.(i) with
    | Some t -> t
    | None -> begin
      (* Replace this type with the closure of its bound *)
      assert ((match pol with Neg -> neg_mark | Pos -> pos_mark).(i) = true);
      assert ((match pol with Neg -> pos_mark | Pos -> neg_mark).(i) = false);
      if currently_rewriting.(i) then
        (* FIXME: replace exn once rectypes exist *)
        failwith "Recursive rewriting in GC - rectypes??";
      currently_rewriting.(i) <- true;
      let oldv = old_vars.(i) in
      let bound = match pol with Neg -> oldv.neg | Pos -> oldv.pos in
      match rewrite_styp pol bound with
      | t' -> (currently_rewriting.(i) <- false;
               rw.(i) <- Some t';
               t')
      | exception Exit ->
         (* FIXME: rectype bounds - allocate a new variable? *)
         (* FIXME: do I need a fixpoint to ensure all bounds get updated? *)
         failwith "unimplemented"
    end
  and rewrite_styp pol t =
    let (rest, vs) = styp_uncons env Flexible t in
    let rest = { rest with cons = map_head pol rewrite_styp rest.cons } in
    let t = List.fold_left (fun acc i -> Types.join pol acc (rewrite_var pol i)) rest vs in
    t in

  kept_vars |> Array.iteri (fun i k ->
    match k with
    | Some v ->
       v.pos <- rewrite_styp Pos old_vars.(i).pos;
       v.neg <- rewrite_styp Neg old_vars.(i).neg
    | None -> ());
  (* Bounds filled in, new environment should be well-formed now *)
  wf_env env;
  let res = rewrite_styp pol ty in
  wf_styp pol env res;
  (* Check that unused variables did not get rewritten *)
  old_vars |> Array.iteri (fun i _ ->
     if not pos_mark.(i) then assert (rewrite_pos.(i) = None);
     if not neg_mark.(i) then assert (rewrite_neg.(i) = None));
  res

  (*
    Notes from 1/5/20.
    We want to keep variables occur both positively and negatively,
    *as well* as keeping variables that occur recursively in their own bound.
    (since we have no other rectypes syntax, as yet at least)

    Can do this by computing positive and negative replacements for each variable:
    for variables to be kept, this is the new variable.
    for variables reachable only positively, we try joining all the bounds.
      But we might fail due to recursion, and resort to keeping the variable.
    likewise for variables reachable only negatively.

    Start with an array of pos and neg bounds, all None.
    First add the kept vars, then start computing bounds for vars to be partially kept.
    Finally, process the type.

    This will work, but it sounds like a shit version of Tarjan's SCC algorithm.
    Should I just implement that instead?
    In what way is it different? Could the complexity matter even in principle?

   *)
*)
