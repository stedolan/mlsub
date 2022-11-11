open Tuple_fields
open Typedefs

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)

type field_conflict = [`Missing of field_name | `Extra of field_name option]

type conflict_reason =
  | Incompatible
  | Field of field_conflict

(* FIXME include orig lhs/rhs, don't flip at contravar *)
type 'a subtyping_error_gen =
  { lhs: 'a;
    rhs: 'a;
    lhs_loc: Location.set;
    rhs_loc: Location.set;
    conflict: conflict_reason }
type subtyping_error = (unit, unit) typ subtyping_error_gen
exception SubtypeError of subtyping_error
exception FieldsSubtypeError of (unit, unit) typ tuple_fields subtyping_error_gen

let contravariant_err err =
  {lhs = err.rhs; lhs_loc = err.rhs_loc;
   rhs = err.lhs; rhs_loc = err.lhs_loc;
   conflict = err.conflict}

(* FIXME most uses are making fresh vars above/below something. Refactor? *)
let[@inline] noerror f = try f () with SubtypeError _ -> intfail "subtyping error should not be possible here!"


(* FIXME move these? *)

(* Order variables by binding time.
   Vbound{index=0} is maximal. Order rigid before flex at same level *)
let compare_typ_var a b =
  match a, b with
  | (Vflex _ | Vrigid _), Vbound _ -> -1
  | Vbound _, (Vflex _ | Vrigid _) -> 1

  | Vbound {index=ia; var=va}, Vbound {index=ib; var=vb} ->
     if ia = ib then compare va vb
     else compare ib ia (* reversed *)

  | Vrigid a, Vflex b when Env_level.equal a.level b.level -> -1
  | Vflex a, Vrigid b when Env_level.equal a.level b.level -> 1

  | Vflex a, Vflex b when Env_level.equal a.level b.level ->
     compare a.id b.id
  | Vrigid a, Vrigid b when Env_level.equal a.level b.level ->
     compare a.var b.var

  | (Vflex {level=la;_}|Vrigid{level=la; _}),
    (Vflex {level=lb;_}|Vrigid{level=lb; _}) ->
     let c = Env_level.compare la lb in
     assert (c <> 0); c

let tvjoin ?(base=Tcons (Location.empty, Bot)) vs =
  (* FIXME what if base has vars of its own? *)
  let vs = List.sort_uniq (fun (_, a) (_, b) -> compare_typ_var a b) vs in
  List.fold_left (fun rest (l, var) ->
     match rest with
     | Tcons (_, Bot) -> Tvar (l, var)
     | _ -> Tvjoin (rest, l, var))
    base vs


(*
 * Subtyping, meet and join on constructed types
 *)
let ignore_fields f = Tuple_fields.map_fields (fun _ _ -> Tsimple ()) f
let ignore_cons t = Cons.map ~neg:(fun _ -> Tsimple ()) ~pos:(fun _ -> Tsimple ()) t

let subtype_cons_fields f la af lb bf =
  let err e =
    FieldsSubtypeError
      { lhs_loc = List.concat_map snd la;
        lhs = ignore_fields af;
        rhs_loc = List.concat_map snd lb;
        rhs = ignore_fields bf;
        conflict = Field e } in
  if bf.fopen = `Closed then begin
    if af.fopen = `Open then raise (err (`Extra None));
    (* check dom a ⊆ dom b *)
    List.iter (fun k ->
      match FieldMap.find k bf.fields with
      | exception Not_found -> raise (err (`Extra (Some k)))
      | _ -> ()) af.fnames
  end;
  FieldMap.iter (fun k b ->
    match FieldMap.find k af.fields with
    | exception Not_found -> raise (err (`Missing k))
    | a ->
       try f a b
       with SubtypeError err ->
         let select_field t fs =
           fs |> Tuple_fields.map_fields (fun k' _ ->
             if k = k' then t else Tsimple ()) in
         let lhs = select_field err.lhs af in
         let rhs = select_field err.rhs bf in
         raise (FieldsSubtypeError {err with lhs; rhs})
    ) bf.fields

let subtype_cons ~pos ~neg (la : cons_locs) a (lb : cons_locs) b =
  let open Cons in
  match a, b with
  | Bot, _ | _, Top -> ()
  | Bool, Bool -> ()
  | Int, Int -> ()
  | String, String -> ()
  | Func (args, res), Func (args', res') ->
     begin match subtype_cons_fields neg lb args' la args with
     | exception (FieldsSubtypeError err) ->
        let err = contravariant_err err in
        raise (SubtypeError {err with lhs = Tcons (la, Func (err.lhs, Tsimple ()));
                                      rhs = Tcons (lb, Func (err.rhs, Tsimple ()))})
     | () ->
        try pos res res'
        with SubtypeError err ->
          raise (SubtypeError {err with lhs = Tcons (la, Func (ignore_fields args, err.lhs));
                                        rhs = Tcons (lb, Func (ignore_fields args', err.rhs))})
     end
  | Record fs, Record fs' ->
     begin match subtype_cons_fields pos la fs lb fs' with
     | () -> ()
     | exception (FieldsSubtypeError err) ->
        raise (SubtypeError {err with lhs = Tcons (la, Record err.lhs);
                                      rhs = Tcons (lb, Record err.rhs)})
     end
  | a,b ->
     raise (SubtypeError {
       lhs_loc = List.concat_map snd la;
       lhs = Tcons (la, ignore_cons a);
       rhs_loc = List.concat_map snd lb;
       rhs = Tcons (lb, ignore_cons b);
       conflict = Incompatible })

(* NB: nleft/nright/nboth = contravariant
   Since meet is used on negative types, these will be *positive* *)
let meet_cons
  ~nleft ~nright ~nboth
  ~pleft ~pright ~pboth
  a b =
  let open Cons in
  match a, b with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | c, Top -> Cons.map ~neg:nleft ~pos:pleft c
  | Top, c' -> Cons.map ~neg:nright ~pos:pright c'
  | Bool, Bool -> Bool
  | Int, Int -> Int
  | String, String -> String
  | (Bool|Int|String), _ | _, (Bool|Int|String) -> Bot
  | Record _, Func _ | Func _, Record _ -> Bot
  | Record c, Record c' ->
     begin match Tuple_fields.union ~left:pleft ~right:pright ~both:pboth c c' with
     | Some r -> Record r
     | None -> Bot
     end
  | Func (args, res), Func (args', res') ->
     (* FIXME: fail here rather than assuming variadic functions?
        Could/should enforce that functions are always `Closed *)
     let args = Tuple_fields.inter ~both:nboth args args' in
     Func (args, pboth res res')

let join_cons
  ~nleft ~nright ~nboth
  ~pleft ~pright ~pboth
  a b =
  let open Cons in
  match a, b with
  | Top, _ | _, Top -> Top
  | c, Bot -> Cons.map ~neg:nleft ~pos:pleft c
  | Bot, c' -> Cons.map ~neg:nright ~pos:pright c'
  | Bool, Bool -> Bool
  | Int, Int -> Int
  | String, String -> String
  | (Bool|Int|String), _ | _, (Bool|Int|String) -> Top
  | Record _, Func _ | Func _, Record _ -> Top
  | Record c, Record c' ->
     Record (Tuple_fields.inter ~both:pboth c c')
  | Func (args, res), Func (args', res') ->
     begin match Tuple_fields.union ~left:nleft ~right:nright ~both:nboth args args' with
     | Some r -> Func (r, pboth res res')
     | None -> Top
     end

(* There are two ways to represent a constraint α ≤ β between two flexible variables.
   (I). Make the upper bound of α be UBvar β. (Ensure also that LB(β) contains LB(α))
   (II). Make the lower bound of β contain α. (Ensure also that UB(α) contains UB(β)) *)


(*
 * Core subtyping functions
 *)

(* preserves order of fv1 *)
let union_flexvars fv1 fv2 =
  fv1 @ List.filter (fun v -> not (List.memq v fv1)) fv2

(* add some flexvars to a join.
   does not check levels, so level of resulting join may increase *)
let join_flexvars lower vs =
  if lower.ctor.cons = Top then lower
  else
    match List.filter (fun v -> not (List.memq v lower.flexvars)) vs with
    | [] -> lower
    | vs -> { lower with flexvars = lower.flexvars @ vs }

(* Check whether a flex-flex constraint α ≤ β is already present via an upper bound of α *)
let rec has_flex_upper (pv : flexvar) nv =
  pv == nv || pv.upper |> List.exists (function
  | UBvar pv' -> has_flex_upper pv' nv
  | UBcons _ -> false)

let rec subtype_t_var ~changes env (p : flex_lower_bound) (nv : flexvar) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_flex ~changes env pv nv);
  subtype_cons_flex ~changes env p.ctor nv

and subtype_t_cons ~changes env (p : flex_lower_bound) (cn : (flex_lower_bound, flexvar) ctor_ty) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_cons ~changes env pv cn);
  subtype_ctor_rig ~changes env p.ctor cn

and subtype_cons_cons ~changes env (lp, cp) (ln, cn) =
  subtype_cons
    ~neg:(subtype_t_var ~changes env)
    ~pos:(subtype_t_var ~changes env) lp cp ln cn

and subtype_ctor_rig ~changes env cp cn =
  Rvset.to_list_loc cp.rigvars |> List.iter (fun (pv, pvloc) ->
    if Rvset.contains cn.rigvars pv then ()
    else
      try subtype_cons_cons ~changes env (env_rigid_bound env pv) (cn.cons_locs, cn.cons)
      with SubtypeError _ ->
        (* FIXME keep parts of err? *)
        let rhs_loc =
          (List.map snd cn.cons_locs) @ (List.map snd (Rvset.to_list_loc cn.rigvars))
          |> List.concat in
        raise (SubtypeError {
          lhs_loc = pvloc;
          rhs_loc;
          lhs = Tvar (pvloc, Vrigid pv);
          rhs = tvjoin ~base:(Tcons (cn.cons_locs, ignore_cons cn.cons))
                  (cn.rigvars |> Rvset.to_list_loc |> List.map (fun (r, l) -> l, Vrigid r));
          conflict = Incompatible;
        }));
  try subtype_cons_cons ~changes env (cp.cons_locs, cp.cons) (cn.cons_locs, cn.cons)
  with SubtypeError err ->
    let rhs_loc = err.rhs_loc @ List.concat (List.map snd (Rvset.to_list_loc cn.rigvars)) in
    raise (SubtypeError {
          lhs_loc = err.lhs_loc;
          rhs_loc;
          lhs = err.lhs;
          rhs = tvjoin ~base:err.rhs
                  (cn.rigvars |> Rvset.to_list_loc |> List.map (fun (r, l) -> l, Vrigid r));
          conflict = err.conflict;               
    })

and subtype_flex_flex ~changes env (pv : flexvar) (nv : flexvar) =
  (* We can record pv <= nv either as an upper bound on pv or a lower bound on nv.
     If they are not at the same level, our choice is forced.
     Otherwise, make an upper bound on pv, unless that would:
       - give pv two upper bounds, or
       - create a cycle of upper bounds *)
  if has_flex_upper pv nv || List.memq pv nv.lower.flexvars then ()
  else begin
    if Env_level.extends nv.level pv.level
       && not (has_flex_upper nv pv) (* avoid creating cycles *)
       && (pv.upper = [] || not (Env_level.equal nv.level pv.level)) (* avoid creating multiple UBs, if possible *) then begin
      fv_set_upper ~changes pv (UBvar nv :: pv.upper);
      subtype_t_var ~changes env pv.lower nv;
    end else begin
      assert (Env_level.extends pv.level nv.level);
      rotate_flex ~changes env pv;
      fv_set_lower ~changes nv (join_flexvars nv.lower [pv]);
      nv.upper |> List.iter (function
        | UBvar nv -> subtype_flex_flex ~changes env pv nv
        | UBcons cn -> subtype_flex_cons ~changes env pv cn)
    end
  end

and rotate_flex ~changes env (pv : flexvar) =
  let rotate, keep = pv.upper |> List.partition (function
     | UBvar v' -> Env_level.equal v'.level pv.level
     | UBcons _ -> false) in
  match rotate with
  | [] -> ()
  | rotate ->
     (* make sure this var stays rotated by giving it a dummy UBcons bound if needed *)
     let keep = match keep with [] -> [UBcons {cons=Top; rigvars=pv.lower.ctor.rigvars; cons_locs=[]}] | k -> k in
     fv_set_upper ~changes pv keep;
     rotate |> List.iter (function
       | UBcons _ -> assert false
       | UBvar v' -> noerror (fun () -> subtype_flex_flex ~changes env pv v'))

and subtype_flex_cons ~changes env pv cn =
  if cn.cons <> Top then begin
    let cploc, cp = ensure_upper_matches ~changes env pv (map_ctor_rig id ignore cn) in
    subtype_cons
      ~neg:(fun _ () -> () (* already done in ensure_upper_matches *))
      ~pos:(subtype_flex_flex ~changes env)
      cploc cp
      cn.cons_locs cn.cons
  end

(* Ensure every rigvar appearing in a flexvar's lower bounds also
   appears in its constructed upper bounds.
     rv <= a <= C implies rv <= a <= C | rv since rv <= C is C = C | rv *)
and ensure_rigvars_present ~changes env (fv : flexvar) =
  let rvlow = fv.lower.ctor.rigvars in
  if Rvset.is_empty rvlow then ()
  else
     let keep, recheck = fv.upper |> List.partition (function
       | UBvar _ -> true
       | UBcons {cons=_;rigvars;cons_locs=_} ->
          Rvset.to_list rvlow |> List.for_all (fun rv -> Rvset.contains rigvars rv)) in
     match recheck with
     | [] -> ()
     | recheck ->
        fv_set_upper ~changes fv keep;
        recheck |> List.iter (function
          | UBvar _ -> assert false
          | UBcons cb ->
            let cb = { cb with rigvars = Rvset.join cb.rigvars rvlow } in
            (* This shouldn't fail because we already have fv <= cb *)
            noerror (fun () -> subtype_flex_cons ~changes env fv cb))

(* Ensure pv has a UBcons upper bound whose head is below a given ctor.
   Returns the constructed upper bound. *)
and ensure_upper_matches ~changes env (pv : flexvar) (cn : (flex_lower_bound, unit) ctor_ty) : _ * (unit, flexvar) Cons.t =
  let cnrig = Rvset.filter (fun rv -> Env_level.extends rv.level pv.level) cn.rigvars in
  let cnrig_drop_locs =
    Rvset.filter (fun rv -> not (Env_level.extends rv.level pv.level)) cn.rigvars
    |> Rvset.to_list_loc |> List.map snd in
  let cbs_match, up_rest = List.partition (function UBvar _ -> false | UBcons cb -> Rvset.equal cnrig cb.rigvars) pv.upper in
  let cbloc, cb, new_rvset =
    match cbs_match with
    | [] -> Location.empty, Cons.Top, true
    | [UBcons c] -> c.cons_locs, c.cons, false
    | _ -> intfail "duplicate bounds with same rigvar set" in
  let cbnew =
    meet_cons
      ~nleft:id
      ~nright:(fun b -> join_lower ~changes env pv.level bottom b)
      ~nboth:(fun a b -> join_lower ~changes env pv.level a b)
      ~pleft:id
      ~pright:(fun _ -> fresh_flexvar pv.level)
      ~pboth:(fun v _ -> v)
      cb cn.cons in
  if not (Cons.equal ~neg:equal_flex_lower_bound ~pos:equal_flexvar cb cbnew) then begin
    let bound = { cons = cbnew; rigvars = cnrig; cons_locs = cn.cons_locs @ (List.map (fun l -> Cons.Bot, l) cnrig_drop_locs) } in
    fv_set_upper ~changes pv (UBcons bound :: up_rest);
    rotate_flex ~changes env pv; (* improves sharing between match vars *)
    subtype_t_cons ~changes env pv.lower bound;
    if new_rvset then ensure_rigvars_present ~changes env pv;
  end;
  cbloc, Cons.map ~neg:ignore ~pos:id cbnew

(* earlier versions did (the equivalent of) a rotate_flex on nv here, but I don't think it helps  *)
and subtype_cons_flex ~changes env (cp : (flexvar, flex_lower_bound) ctor_ty) (nv : flexvar) =
  let lower = join_lower ~changes env nv.level nv.lower {ctor=cp;flexvars=[]} in
  (* Printf.printf "lower bound of %a: %a --> %a\n" pp_flexvar nv pp_flexlb nv.lower pp_flexlb lower; *)
  (* FIXME hoisting: is cp OK? shouldn't we compare against lower? Might that be different? *)
  if fv_maybe_set_lower ~changes nv lower then begin
    nv.upper |> List.iter (function
      | UBvar v -> subtype_cons_flex ~changes env cp v
      | UBcons c -> subtype_ctor_rig ~changes env cp c);
    ensure_rigvars_present ~changes env nv;
  end

and join_ctor ~changes env level lower cp =
  (* lower is already wf at level, cp may not be *)
  let cons =
    join_cons
       ~nleft:id
       ~nright:(fun y ->
         (* Not fresh_below_var, as hoisting may be needed.
            FIXME test this *)
         let v = fresh_flexvar level in
         noerror (fun () -> subtype_flex_flex ~changes env v y); v)
       ~nboth:(fun x y ->
         noerror (fun () -> subtype_flex_flex ~changes env x y); x)
       ~pleft:id
       (* NB: pright is not id, because we need fresh variables for contravariant parts,
          to preserve matchability *)
       ~pright:(fun x -> join_lower ~changes env level bottom x)
       ~pboth:(fun x y -> join_lower ~changes env level x y)
       lower.cons cp.cons in
  Rvset.fold (fun c (rv, l) ->
    if Rvset.contains c.rigvars rv then c
    else if Env_level.extends rv.level level then
      { c with rigvars = Rvset.add c.rigvars rv l }
    else
      let cons_locs, cons = env_rigid_bound env rv in
      let cons_locs =
        (* If the upper bound is trivial, keep the location of the rv *)
        match cons with
        | Top -> [Cons.Top, l]
        | _ -> cons_locs in
      join_ctor ~changes env level c {cons; rigvars=Rvset.empty; cons_locs})
    { cons; rigvars = lower.rigvars; cons_locs=lower.cons_locs@cp.cons_locs }
    cp.rigvars

and join_lower ~changes env level {ctor=ca; flexvars=fva} {ctor=cb; flexvars=fvb} =
  (* (ca,fva) is already wf at level, (cb,fvb) may not be *)
  let ctor = join_ctor ~changes env level ca cb in
  if ctor.cons = Top then {ctor; flexvars=[]} else
  let fvb = fvb |> List.map (fun fv ->
    (* FIXME cache hoisted vars? ditto above. check all fresh_flexvar calls! *)
    if Env_level.extends fv.level level then fv
    else
      let fv' = fresh_flexvar level in
      noerror (fun () -> subtype_flex_flex ~changes env fv fv'); fv') in
  let lb = join_flexvars {ctor; flexvars=fva} fvb in
  lb

(*
 * Subtyping on typs (polymorphism)
 *)

(* check that a well-formed type is simple (i.e does not contain a forall) *)
let rec check_simple = function
  | Tsimple _ | Tvar _ -> true
  | Tvjoin _ ->
     (* Anything under the join must be simple by wf-ness *)
     true
  | Tcons (_, c) ->
     Cons.equal ~neg:(=) ~pos:(=)
       (Cons.map ~neg:(fun _ -> true) ~pos:(fun _ -> true) c)
       (Cons.map ~neg:check_simple ~pos:check_simple c)
  | Tpoly _ -> false

(* argument must be a simple locally closed type well-formed in env *)
let rec simple_ptyp env : ptyp -> flex_lower_bound = function
  | Tsimple t -> t
  | Tcons (l, cp) ->
     let cons = Cons.map ~neg:(simple_ntyp_var env) ~pos:(simple_ptyp env) cp in
     { ctor = { cons; rigvars = Rvset.empty; cons_locs = l } ; flexvars = [] }
  | Tpoly _ -> intfail "simple_ptyp: Tpoly is not simple"
  | Tvjoin (_, _, Vbound _) | Tvar (_, Vbound _) -> intfail "simple_ptyp: not locally closed"
  | Tvar (_, Vflex fv) ->
     assert (Env_level.extends fv.level (env_level env));
     { ctor = {cons=Bot;rigvars=Rvset.empty;cons_locs=[]}; flexvars = [fv] }
  | Tvar (l, Vrigid rv) ->
     assert (Env_level.extends rv.level (env_level env));
     { ctor = {cons=Bot; rigvars=Rvset.singleton rv l; cons_locs=[]}; flexvars = [] }
  | Tvjoin (t, _, Vflex fv) ->
     assert (Env_level.extends fv.level (env_level env));
     join_flexvars (simple_ptyp env t) [fv]
  | Tvjoin (t, l, Vrigid rv) ->
     assert (Env_level.extends rv.level (env_level env));
     let {ctor={cons;rigvars;cons_locs};flexvars} = simple_ptyp env t in
     {ctor={cons;rigvars=Rvset.add rigvars rv l;cons_locs};flexvars}

and simple_ntyp env : ntyp -> styp_neg = function
  | Tsimple t -> UBvar t
  | Tcons (l, cn) ->
     UBcons {cons = Cons.map ~neg:(simple_ptyp env) ~pos:(simple_ntyp_var env) cn;
             rigvars=Rvset.empty;
             cons_locs = l}
  | Tpoly _ -> intfail "simple_ntyp: Tpoly is not simple"
  | Tvjoin (_, _, Vbound _) | Tvar (_, Vbound _) -> intfail "simple_ntyp: not locally closed"
  | Tvar (_, Vflex fv) ->
     assert (Env_level.extends fv.level (env_level env));
     UBvar fv
  | Tvar (l, Vrigid rv) ->
     assert (Env_level.extends rv.level (env_level env));
     UBcons {cons=Bot; rigvars=Rvset.singleton rv l; cons_locs=[]}
  | Tvjoin (_, _, Vflex _) -> intfail "simple_ntyp: negative join"
  | Tvjoin (t, l, Vrigid rv) ->
     assert (Env_level.extends rv.level (env_level env));
     match simple_ntyp (env_at_level env rv.level) t with
     | UBvar _ -> intfail "simple_ntyp: rigid/flex negative join"
     | UBcons {cons;rigvars;cons_locs} ->
        UBcons {cons;rigvars = Rvset.add rigvars rv l; cons_locs}

and simple_ntyp_var env (t : ntyp) : flexvar =
  match simple_ntyp env t with
  | UBvar v -> v
  | UBcons cn ->
     let fv = fresh_flexvar (env_level env) in
     noerror (fun () -> subtype_flex_cons ~changes:(ref []) env fv cn);
     fv

let instantiate_flex env vars body =
  let fvars = IArray.map (fun _ -> fresh_flexvar (env_level env)) vars in
  IArray.iter2 (fun (fv : flexvar) (_,t) ->
    let b = [simple_ntyp env (open_typ_flex fvars t)] in
    assert (fv.upper = [] && is_bottom fv.lower);
    fv_set_upper ~changes:(ref []) fv b) fvars vars;
  open_typ_flex fvars body

let enter_rigid env vars rig_names =
  let level = Env_level.extend (env_level env) in
  let rvars = IArray.mapi (fun var _ -> {level; var}) vars in
  let temp_env =
    Env_types { level; rig_names;
                rig_defns = IArray.map (fun (name, _) ->
                    {name; upper=Top; upper_locs=Location.empty}) vars; rest = env } in
  let rig_defns = IArray.map (fun (name, b) ->
     let upper = simple_ptyp temp_env (open_typ_rigid rvars b) in
     (* FIXME: can you actually hit this?
        Try with a higher-rank type where the outer rank gets instantiated.
        Maybe change the type of the upper bound in parsed types.
        (to reflect its Tconsness)*)
     assert (upper.flexvars = []);
     assert (Rvset.is_empty upper.ctor.rigvars);
     { name; upper = upper.ctor.cons; upper_locs=upper.ctor.cons_locs }) vars in
  let env = Env_types { level; rig_names; rig_defns; rest = env} in
  env, rvars

(* arg must be locally closed, not necessarily simple *)
let rec approx_ptyp env : ptyp -> flex_lower_bound = function
  | Tcons (l, cp) ->
     let cons = Cons.map ~neg:(approx_ntyp_var env) ~pos:(approx_ptyp env) cp in
     { ctor = { cons; rigvars = Rvset.empty; cons_locs = l }; flexvars = [] }
  | (Tvar _ | Tvjoin _ | Tsimple _) as t -> simple_ptyp env t
  | Tpoly {vars;body} ->
     let body = instantiate_flex env vars body in
     approx_ptyp env body


(* FIXME hoisting below here *)
and approx_ntyp env : ntyp -> styp_neg = function
  | Tcons (l, cn) ->
     let cons = Cons.map ~neg:(approx_ptyp env) ~pos:(approx_ntyp_var env) cn in
     UBcons {cons;rigvars=Rvset.empty;cons_locs = l}
  | (Tvar _ | Tvjoin _ | Tsimple _) as t ->
     simple_ntyp env t
  | Tpoly {vars; body} ->
     (* Negative var occurrences should be replaced with their upper
        bounds, positive ones should be deleted. *)
     let bounds = Array.make (IArray.length vars) None in
     let neg rest _l v =
       (match rest with Some _ -> intfail "contravariant join" | None -> ());
       match bounds.(v) with
       | None -> intfail "recursive rigid bound"
       | Some t -> Tsimple t in
     let pos rest _l _v =
       match rest with
       | None -> Tcons ([], Bot)
       | Some t -> t in
     vars |> IArray.iteri (fun i (_, b) ->
       let b = open_typ ~neg:pos ~pos:neg 0 b in
       let b = approx_ptyp env b in
       bounds.(i) <- Some b);
     let body = open_typ ~neg ~pos 0 body in
     approx_ntyp env body

and approx_ntyp_var env (n : ntyp) : flexvar =
  match approx_ntyp env n with
  | UBvar v -> v
  | UBcons cons ->
     let fv = fresh_flexvar (env_level env) in
     noerror (fun () -> subtype_flex_cons ~changes:(ref []) env fv cons);
     fv


(* FIXME: not ideal, probably copies too many vars *)
let join_simple env p q =
  let r = bottom in
  let r = join_lower ~changes:(ref []) env (env_level env) r p in
  let r = join_lower ~changes:(ref []) env (env_level env) r q in
  r

(* FIXME: rank1 joins maybe?
   FIXME: keep types as Tcons if possible? Better inference. Can this matter? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  Tsimple (join_simple env (approx_ptyp env p) (approx_ptyp env q))

let match_cons ~changes env (cons_locs, cons) (loc, head) =
  subtype_cons cons_locs cons loc head
    ~neg:(subtype_t_var ~changes env)
    ~pos:(fun p r -> r := join_lower ~changes env (env_level env) !r p)

let match_simple_typ ~changes env (p : flex_lower_bound) loc (head : (flex_lower_bound, flex_lower_bound ref) Cons.t) =
  let {ctor = {cons; rigvars; cons_locs}; flexvars} = p in
  match_cons ~changes env (cons_locs, cons) (loc, head);
  Rvset.to_list_loc rigvars |> List.iter (fun (rv, rvloc) ->
    try match_cons ~changes env (env_rigid_bound env rv) (loc, head)
    with SubtypeError err ->
      raise (SubtypeError {
        lhs_loc = rvloc;
        rhs_loc = err.rhs_loc;
        lhs = Tvar (rvloc, Vrigid rv);
        rhs = err.rhs;
        conflict = Incompatible;
      }));
  flexvars |> List.iter (fun fv ->
    let mhead = Cons.map ~neg:id ~pos:ignore head in
    let mloc, m = ensure_upper_matches ~changes:(ref []) env fv {cons=mhead;rigvars=Rvset.empty;cons_locs=loc} in
    noerror (fun () -> subtype_cons mloc m loc head
      ~neg:(fun _t () -> () (*already filled*))
      ~pos:(fun v r -> r := join_flexvars !r [v])));
  ()


let rec subtype env (p : ptyp) (n : ntyp) =
  (* Format.printf "%a <= %a\n" pp_ptyp p pp_ntyp n; *)
  wf_ptyp env p; wf_ntyp env n;
  match p, n with
  | Tcons (lp, cp), Tcons (ln, cn) ->
     subtype_cons ~neg:(subtype env) ~pos:(subtype env) lp cp ln cn
  | p, Tpoly {vars; body} ->
     (* FIXME: scoping in errors *)
     let env, rvars = enter_rigid env vars SymMap.empty in
     let body = open_typ_rigid rvars body in
     subtype env p body; ()
  | Tpoly {vars; body}, n ->
     (* FIXME: scoping in errors *)
     let level = Env_level.extend (env_level env) in
     let env = Env_types { level; rig_names = SymMap.empty; rig_defns = IArray.empty; rest = env } in
     let body = instantiate_flex env vars body in
     subtype env body n; ()
  | p, Tcons (ln, cn) ->
     (* FIXME errors & Tpoly instantiation? *)
     let shead = Cons.map ~neg:(approx_ptyp env) ~pos:(fun _ -> ref bottom) cn in
     match_simple_typ ~changes:(ref []) env (approx_ptyp env p) ln shead;
     subtype_cons Location.empty shead Location.empty cn
       ~neg:(fun _ _ -> () (* already done above *))
       ~pos:(fun p n -> subtype env (Tsimple !p) n)
  | p, ((Tsimple _ | Tvar _ | Tvjoin _) as n) ->
     subtype_t_var ~changes:(ref []) env (approx_ptyp env p) (approx_ntyp_var env n); ()

let subtype env p n =
  (* FIXME: revert changes on failure? *)
  match subtype env p n with
  | () -> Ok ()
  | exception SubtypeError e -> Error e

let rec match_typ env (p : ptyp) loc head =
  match p with
  | Tcons (lc,c) ->
     subtype_cons lc c loc head
       ~neg:(fun (_,v) t -> assert (!v = Tcons (Location.empty, Top)); v := t)
       ~pos:(fun t (_,v) -> assert (!v = Tcons (Location.empty, Bot)); v := t);
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_typ env body loc head
  | t ->
     let instneg (_,v) =
       let fv = fresh_flexvar (env_level env) in
       v := Tsimple fv;
       simple_ptyp env (Tvar (Location.empty, Vflex fv)) in
     let shead = Cons.map ~neg:instneg ~pos:(fun _ -> ref bottom) head in
     match_simple_typ ~changes:(ref []) env (approx_ptyp env t) loc shead;
     noerror (fun () -> subtype_cons Location.empty shead Location.empty head
       ~neg:(fun _ _ -> () (*already inserted by instneg*))
       ~pos:(fun t (_,v) -> v := Tsimple !t))

let match_typ env ty loc head =
  let loc = mk_cons_locs loc head in
  let head = Cons.map ~neg:(fun x -> x, ref (Tcons (Location.empty, Top))) ~pos:(fun x -> x, ref (Tcons (Location.empty, Bot))) head in
  wf_ptyp env ty;
  match match_typ env ty loc head with
  | () ->
     wf_ptyp env ty;
     Ok (Cons.map ~neg:(fun (x, r) -> x, !r) ~pos:(fun (x, r) -> x, !r) head)
  | exception SubtypeError e ->
     Error e



(*
 * Generalisation
 *)


(* Speculative subtyping.
   Dodgy, order-dependent, and probably not principal.
   In its defence:
     (a) only used during generalisation, where order is visible and
         nonprincipality only risks β-expansion (I think?)
     (b) only matters in higher-rank / checked rigvar contexts, where
         nonprincipality is less of an issue *)
let spec_sub_rigid_cons env (rv : rigvar) cn =
  let changes = ref [] in
  match subtype_ctor_rig ~changes env
          {cons=Bot; rigvars=Rvset.singleton rv Location.empty; cons_locs=[]} cn with
  | () when !changes = [] -> true
  | () ->
     (* Dubious case: we could also choose to keep these changes *)
     revert !changes; false
  | exception SubtypeError _ ->
     revert !changes; false

let spec_sub_rigid_pos env (rv : rigvar) p =
  let changes = ref [] in
  let cons_locs, cons = env_rigid_bound env rv in
  match join_lower ~changes env (env_level env) p {ctor={cons;rigvars=Rvset.empty;cons_locs};flexvars=[]} with
  | p' when equal_flex_lower_bound p p' && !changes = [] -> true
  | _ -> revert !changes; false


(* Returns true only if a <= b
   Not complete, never changes anything.
   Used only for optimisations, to avoid generalising a when x <= a <= x.
   Not a bug if it spuriously returns false sometimes (but leads to uglier types) *)
let rec clearly_subtype (a :  flexvar) ({ctor; flexvars} as b : flex_lower_bound) : bool =
  ctor.cons = Top ||
  List.memq a flexvars ||
  a.upper |> List.exists (function
  | UBvar a -> clearly_subtype a b
  | UBcons cn ->
    Rvset.to_list cn.rigvars |> List.for_all (fun rv ->
      Rvset.contains ctor.rigvars rv) &&
    match
      subtype_cons cn.cons_locs cn.cons ctor.cons_locs ctor.cons
        ~neg:(fun a b -> if not (clearly_subtype a b) then raise Exit)
        ~pos:(fun a b -> if not (clearly_subtype a b) then raise Exit)
    with
    | exception SubtypeError _ -> false
    | () -> true)



(* FIXME: I think this is all dodgy re flexvars at upper levels
   Are there enough level checks in expand / substn? *)
(* FIXME: how does this work with rigvars & flexvars at the same level? (i.e. poly fns) *)
(* FIXME: Probably every error:noerror below is wrong *)


let hoist_flex ~changes env level v =
  if Env_level.extends v.level level then ()
  else begin
    (* This might not be efficient: maybe better to hoist more eagerly *)
    let lower = v.lower and upper = v.upper in
    fv_set_lower ~changes v bottom;
    fv_set_upper ~changes v [];
    fv_set_level ~changes v level;
    subtype_t_var ~changes env lower v;
    upper |> List.iter (function
      | UBvar v' -> subtype_flex_flex ~changes env v v'
      | UBcons c -> subtype_flex_cons ~changes env v c)
  end

let rec hoist_lower ~changes env level {ctor;flexvars} =
  (* FIXME hoisting: this looks wrong: what about the levels of ctor.rigvars?  *)
  map_ctor_rig (hoist_flex ~changes env level) (hoist_lower ~changes env level) ctor |> ignore;
  List.iter (hoist_flex ~changes env level) flexvars;
  ()


let rec expand visit ~changes ?(vexpand=[]) env (p : flex_lower_bound) =
  let level = env_level env in
  wf_flex_lower_bound ~seen:(Hashtbl.create 10) env level p;
  let flexvars_gen, flexvars_keep = List.partition (fun fv -> Env_level.equal fv.level level) p.flexvars in
  flexvars_gen |> List.iter (fun pv ->
    fv_gen_visit_pos env visit pv (function
    | First_visit ->
       (* This var is +-reachable, so rotate. (It's unlikely to be deleted by subst_fv_neg) *)
       rotate_flex ~changes env pv;
       (* Add pv to vexpand so we know to ignore it if we see it again before going
          under a constructor. (This is basically a bad quadratic SCC algorithm) *)
       let lower = expand visit ~changes ~vexpand:(pv :: vexpand) env pv.lower in
       (* We may have hoisted the variable during that expansion, so check if we
          still need to generalise it *)
       if Env_level.equal pv.level level then begin
         (* Remove useless reflexive constraints, if they appeared by expanding a cycle *)
         let lower = { lower with flexvars = List.filter (fun v -> not (equal_flexvar v pv)) lower.flexvars } in
         if fv_maybe_set_lower ~changes pv lower then
           ensure_rigvars_present ~changes env pv;
       end
    | Recursive_visit ->
       (* recursive occurrences are fine if not under a constructor *)
       if List.memq pv vexpand then ()
       else unimp "positive recursion on flexvars"));

  (* Avoid making invalid Tvjoins by hoisting if needed *)
  let keep_level =
    List.fold_left
      (fun level fv -> if Env_level.extends fv.level level then fv.level else level)
      level flexvars_keep in


  let p = { p with flexvars = [] } in
  let p =
    (* FIXME: noerror? *)
    if Env_level.equal level keep_level then p
    else noerror (fun () -> 
          hoist_lower ~changes env keep_level p;
          join_lower ~changes env keep_level bottom p)in

  let cons = Cons.map ~neg:(expand_fv_neg visit ~changes env) ~pos:(expand visit ~changes env) p.ctor.cons in
  let rigvars = p.ctor.rigvars |> Rvset.filter (fun rv ->
    not (spec_sub_rigid_pos env rv {ctor={cons;rigvars=Rvset.empty;cons_locs=p.ctor.cons_locs};flexvars=[]})) in
  let ctor = { cons; rigvars; cons_locs=p.ctor.cons_locs } in

  (* NB: flexvars_gen occurs twice below, re-adding the reflexive constraints: α expands to (α|α.lower) *)
  (* NB: this is careful to preserve order if no change is made *)
  let { ctor; flexvars = flexvars_exp } =
    List.fold_left (fun p v -> join_lower ~changes env level p v.lower)
      { ctor; flexvars = flexvars_keep }
      flexvars_gen in
  let flexvars_exp_gen, flexvars_keep = List.partition (fun fv -> Env_level.equal fv.level level) flexvars_exp in
  (* C|a = C, if a <= C, so we might be able to drop some flexvars *)
  let flexvars_gen =
    union_flexvars flexvars_gen flexvars_exp_gen
    |> List.filter (fun fv -> not (clearly_subtype fv {ctor;flexvars=flexvars_keep})) in
  {ctor; flexvars=flexvars_keep @ flexvars_gen}


and expand_fv_neg visit ~changes env nv =
  fv_gen_visit_neg env visit nv (function
  | Recursive_visit ->
     intfail "neg cycle found on %s but rec types not implemented!" (flexvar_name nv)
  | First_visit ->
    (* Ensure there is at most one upper bound *)
    let level = env_level env in
    let rec collect level vars cns = function
      | [] -> level, List.rev vars, List.rev cns
      | UBvar v :: rest ->
         collect (Env_level.min level v.level) (v :: vars) cns rest
      | UBcons cn :: rest ->
         let cn = map_ctor_rig (expand visit ~changes env) (expand_fv_neg visit ~changes env) cn in
         collect level vars (cn :: cns) rest in
    match collect level [] [] nv.upper with
    | vlevel, _, _ when not (Env_level.equal level vlevel) ->
       noerror (fun () -> hoist_flex ~changes env vlevel nv)
    | _, [], [] -> ()
    | _, [v], [] -> ignore (expand_fv_neg visit ~changes env v)
    | _, [], [cn] -> ignore (fv_maybe_set_upper ~changes nv [UBcons cn])
    | _, vars, cns ->
       let cons_locs = List.concat_map (fun cn -> cn.cons_locs) cns in
       let all_rigvars = List.fold_left (fun s c -> Rvset.join s c.rigvars) Rvset.empty cns in
       let keep_rigvars = all_rigvars |> Rvset.filter (fun rv ->
         cns |> List.for_all (fun cn -> spec_sub_rigid_cons env rv cn)) in
       fv_set_upper ~changes nv [UBcons {cons=Top; rigvars = keep_rigvars; cons_locs}];
       (* FIXME noerror? *)
       noerror (fun () ->
         cns |> List.iter (fun cn ->
           subtype_flex_cons ~changes env nv {cn with rigvars = keep_rigvars });
         assert (List.length nv.upper <= 1);
         (* FIXME hoisting: what if something just got hoisted? Can that happen? *)
         vars |> List.iter (fun v ->
           subtype_flex_flex ~changes env nv v))
  );
  nv

(* This function could be optimised by skipping subtrees that have no use
   of the outermost level, Remy-style *)
let rec map_typ_simple : 'neg 'pos .
  neg:(index:int -> ('pos,'neg) typ -> ('pos, 'neg) typ) ->
  pos:(index:int -> ('neg,'pos) typ -> ('neg, 'pos) typ) ->
  index:int -> ('neg, 'pos) typ -> ('neg, 'pos) typ =
  fun ~neg ~pos ~index -> function
  | Tcons (l,c) ->
     Tcons (l,Cons.map
              ~neg:(map_typ_simple ~pos:neg ~neg:pos ~index)
              ~pos:(map_typ_simple ~neg ~pos ~index)
              c)
  | Tvjoin (t, l, Vbound v) -> Tvjoin(map_typ_simple ~neg ~pos ~index t, l, Vbound v)
  | Tvar (l, Vbound v) -> Tvar (l, Vbound v)
  | Tsimple _
  | Tvjoin (_, _, (Vflex _ | Vrigid _))
  | Tvar (_, (Vflex _ | Vrigid _)) as t ->
     pos ~index t
  | Tpoly {vars; body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (n, t) -> n, map_typ_simple ~neg:pos ~pos:neg ~index t) vars in
     let body = map_typ_simple ~neg ~pos ~index body in
     Tpoly {vars; body}

let expand_typ visit ~changes env =
  let pos ~index:_ t =
    let t = simple_ptyp env t in
    let t' = expand visit ~changes env t in
    if not (equal_flex_lower_bound t t') then
      changes := Change_expanded_mark :: !changes;
    Tsimple t' in
  let neg ~index:_ t =
    Tsimple (expand_fv_neg visit ~changes env (simple_ntyp_var env t)) in
  map_typ_simple ~neg:pos ~pos:neg ~index:0, map_typ_simple ~neg ~pos ~index:0

let expand_ntyp visit ~changes env = fst (expand_typ visit ~changes env)
let expand_ptyp visit ~changes env = snd (expand_typ visit ~changes env)

(* FIXME: bit weird... There must be a better representation for bvars here *)

type genvar =
  | Gen_flex of flexvar * ntyp
  | Gen_rigid of rigvar

(* 

design:
  switch to a different mode for subst'ing in elaborations
  in elab mode:
    1. don't worry about contravariant joins in substn_upper
    2. if keeping a var that occurs negatively, always expand (even at neg occs)
    3. if bivariant vars don't have a bound ix by now, don't make one (expand & drop)

  3 amounts to replacing vars with their lower bound if not used in gen type.
  Two other classes of vars could in theory be dropped:
    - vars used positively in gen type and negatively only in elab
    - vars used negatively in gen type and positively only in elab

  FIXME: 1 is not implemented yet (requires testing)
 *)

type subst_info = {
  visit: int;
  bvars: genvar Vector.t;
  env: env;
  level: Env_level.t;
  index: int;
  mode: [`Poly | `Elab]
}

let is_visited_pos visit fv =
  match fv.gen with
  | Not_generalising -> assert false
  | Generalising {visit={pos;_};_} ->
     assert (pos land 1 = 0);
     pos = visit

let is_visited_neg visit fv =
  match fv.gen with
  | Not_generalising -> assert false
  | Generalising {visit={neg;_};_} ->
     assert (neg land 1 = 0);
     neg = visit

let rec substn : 'a 'b . subst_info -> flex_lower_bound -> ('a, 'b) typ =
  fun s {ctor={cons;rigvars; cons_locs};flexvars} ->
  let cons = Cons.map ~neg:(substn_fv_neg s) ~pos:(substn s) cons in
  let rigvars_gen, rigvars_keep = Rvset.peel_level s.level rigvars in
  let flexvars_gen, flexvars_keep = List.partition (fun (fv:flexvar) -> Env_level.equal fv.level s.level) flexvars in
  flexvars_gen |> List.iter (fun fv -> assert (is_visited_pos s.visit fv));

  let rigvars_gen = rigvars_gen |> List.map (fun ((rv:rigvar), l) ->
    l, Vbound {index = s.index; var = rv.var}) in
  let rigvars_keep = Rvset.to_list_loc rigvars_keep |> List.map (fun (rv,l) -> l, Vrigid rv) in
  let flexvars_gen = flexvars_gen |> List.filter_map (substn_bvar s) |> List.concat in
  let flexvars_keep = flexvars_keep |> List.map (fun fv -> Location.empty, Vflex fv) in

  tvjoin ~base:(Tcons (cons_locs,cons))
    (rigvars_keep @ flexvars_keep @ rigvars_gen @ flexvars_gen)

and substn_fv_neg : 'a 'b . subst_info -> flexvar -> ('a, 'b) typ =
  fun s nv ->
  assert (Env_level.extends nv.level s.level);
  if Env_level.equal nv.level s.level then begin
    assert (is_visited_neg s.visit nv);
    match s.mode, substn_bvar s nv with
    | `Poly, Some vs -> tvjoin vs
    | `Poly, None -> substn_upper s nv.upper
    | `Elab, _ when not (is_visited_pos s.visit nv) ->
       (* FIXME is this correct? Should Elab- vars be replaced with their *upper* bounds? *)
       substn_upper s nv.upper
    | `Elab, v ->
       assert (is_visited_pos s.visit nv);
       let expansion = substn s nv.lower in
       (* Negative joins, but only in Elab positions *)
       match v with
       | None -> expansion
       | Some vs -> tvjoin ~base:expansion vs
  end else begin
    Tvar (Location.empty, Vflex nv)
  end

(* FIXME: I think there's some refactoring to do between substn_{bvar,upper} *)
and substn_upper : 'a 'b . subst_info -> styp_neg list -> ('a, 'b) typ =
  fun s t ->
  match t with
  | [] -> Tcons (Location.empty, Top)
  | _ :: _ :: _ -> intfail "multirig gen"
  | [UBvar v] -> substn_fv_neg s v
  | [UBcons {cons;rigvars;cons_locs}] ->
     let cons = Cons.map ~neg:(substn s) ~pos:(substn_fv_neg s) cons in
     let rigvars_gen, rigvars_keep = Rvset.peel_level s.level rigvars in
     let rigvars_gen = rigvars_gen |> List.map (fun (v,l) ->
       assert (Vector.get s.bvars v.var = Gen_rigid v);
       l, Vbound {index=s.index; var=v.var}) in
     let rigvars_keep =
       Rvset.to_list_loc rigvars_keep |> List.map (fun (v,l) -> l, Vrigid v) in
     (* FIXME is this still needed? *)
     match cons, rigvars_keep, rigvars_gen, s.mode with
     | Bot, [], [l,v], _ -> Tvar (l,v)
     | cons, rigvars, _, `Poly ->
        (* Drop rigvars_gen to avoid making contravariant joins *)
        List.fold_left (fun c (l,r) -> Tvjoin (c, l, r)) (Tcons (cons_locs,cons)) rigvars
     | cons, rv_keep, rv_gen, `Elab ->
        (* FIXME: this is wrong, I think. Be careful about Tvjoin invariants *)
        List.fold_left (fun c (l,r) -> Tvjoin (c, l, r)) (Tcons (cons_locs,cons)) (rv_keep @ rv_gen)


(* FIXME!!: gen constraints. What can upper bounds be? *)
and substn_bvar s fv =
  assert (Env_level.equal fv.level s.level);
  match fv.gen with
  | Not_generalising ->
     (* FIXME is this possible? *)
     assert false
  | Generalising gen ->
     if not (gen.visit.pos = s.visit && gen.visit.neg = s.visit) then None
     else match gen.bound_var with
     | Computing_bound ->
        unimp "flexvar recursive in own bound"
     | Generalised var ->
        Some [Location.empty, Vbound {index=s.index; var}]
     | Replace_with_rigid rvs ->
        Some (List.map (fun (rv, l) -> l, Vrigid rv) rvs)
     | _ when s.mode = `Elab ->
        None (* Don't generalise a variable just for the sake of Elab *)
     | No_var_chosen ->
       gen.bound_var <- Computing_bound;
       let bv =
         match fv.upper with
         | [] ->
           let n = Vector.push s.bvars (Gen_flex (fv, Tcons (Location.empty, Top))) in
           Generalised n
         | [UBcons {cons;rigvars;cons_locs}] ->
            if
              rigvars |> Rvset.to_list |> List.for_all (fun rv ->
                spec_sub_rigid_cons s.env rv {cons;cons_locs;rigvars=Rvset.empty})
            then
              let bound = substn_upper {s with index=0}
                            [UBcons {cons;rigvars=Rvset.empty;cons_locs}] in
              let n = Vector.push s.bvars (Gen_flex (fv, bound)) in
              Generalised n
            else begin
              let rigvars_gen, rigvars_keep = Rvset.peel_level s.level rigvars in
              match Rvset.to_list_loc rigvars_keep, rigvars_gen with
              | [], [rv,_] ->
                 assert (Env_level.equal rv.level s.level);
                 Generalised rv.var
              | rvs, _ ->
                 (* Drop rigvars_gen to avoid making contravariant joins *)
                 (* FIXME: soundness relies on copies from lower still being included; test this
                    (some example with a subset of rigvars in the lower bound of fv) *)
                 Replace_with_rigid rvs
            end
         | _ -> assert false
       in
       gen.bound_var <- bv;
       substn_bvar s fv

let substn_typ s =
  let simple = function
    | Tsimple t -> t
    | _ -> intfail "subst on unexpanded simple type" in
  let pos ~index t =
    substn {s with index} (simple t) in
  let neg ~index t =
    substn_fv_neg {s with index} (simple t) in
  map_typ_simple ~neg:pos ~pos:neg ~index:s.index, map_typ_simple ~neg ~pos ~index:s.index

let substn_ntyp s : ntyp -> ntyp = fst (substn_typ s)
let substn_ptyp s : ptyp -> ptyp = snd (substn_typ s)
