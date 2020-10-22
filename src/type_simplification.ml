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
