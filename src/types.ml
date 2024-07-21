open Util
open Typedefs

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)

let tjoin ?loc a b =
  match a, b with
  | Tbot _, x -> x
  | x, Tbot _ -> x
  | a, b -> Tjoin (a, b, loc)

let tjoin' ?loc = function
  | [] -> Tbot loc
  | [x] -> x
  | x :: xs -> List.fold_left (tjoin ?loc) x xs

let tvjoin ?(base=Tbot None) vs =
  List.fold_left (fun t v -> tjoin t (Tvar v)) base vs

let tcons cons = Tcons cons

let tcons_head (c, loc) =
  let tunit _ = Tsimple () in
  Tcons (Cons1.map ~neg:tunit ~pos:tunit c, loc)

type conflict =
  | Head of Cons1.head_conflict
  | Sub of Cons1.sub_error

type err_typ = (unit, unit) typ
type subtyping_error = {
  lhs : err_typ;
  rhs : err_typ;
  err : conflict;
  located : (err_typ Location.loc * err_typ Location.loc);
  env : env * string iarray list;
}

exception SubtypeError of subtyping_error

let close_err_rigid ~orig_env ~env vars {lhs; rhs; err; located; env = (_env', ext)} =
  (* Type errors should never involve flexible variables *)
  let close_var v ~ispos:_ ~isjoin:_ =
    match v with
    | Vrigid v -> v.var
    | _ -> intfail "expected rigid var"
  in
  let close ~ispos t =
    close_typ (env_level env) close_var ~simple:id ~ispos ~isjoin:false 0 t
  in
  let lhs = close ~ispos:true lhs in
  let rhs = close ~ispos:false rhs in
  let located =
    located |> (fun ((a,al),(b,bl)) ->
       ((close ~ispos:true a,al), (close ~ispos:false b,bl)))
  in
  let ext = IArray.map (fun ((s,_),_) -> s) vars :: ext in
  { lhs; rhs; err; located; env = (orig_env, ext) }

(* FIXME most uses are making fresh vars above/below something. Refactor? *)
let[@inline] noerror f = try f () with SubtypeError _ -> intfail "subtyping error should not be possible here!"

(*
 * Core subtyping functions
 *)

(* There are two ways to represent a constraint α ≤ β between two flexible variables.
   (I). Make the upper bound of α be UBvar β. (Ensure also that LB(β) contains LB(α))
   (II). Make the lower bound of β contain α. (Ensure also that UB(α) contains UB(β)) *)

let make_err env err (cp,cploc) (cn,cnloc) =
  let lhs = tcons_head (cp, cploc) and rhs = tcons_head (cn, cnloc) in
  { lhs;
    rhs;
    err;
    located = ((lhs, cploc), (rhs, cnloc));
    env = (env, []) }

let make_err_nocons env errs (cp,cploc) (cn,cnloc) =
  let err = Head errs in
  let lhs = tcons_head (cp, cploc) in
  let rhs =
    List.fold_left (fun acc u ->
      match u with
      | Ucons c -> tjoin ~loc:cnloc acc (tcons_head (c, cnloc))
      | Urigvar (_, _ :: _) -> acc (* ignore if delayed constraint. (FIXME?) *)
      | Urigvar (r, []) -> tjoin ~loc:cnloc acc (Tvar (Vrigid r))
    ) (Tbot (Some cnloc)) cn
  in
  { lhs; rhs; err;
    located = ((lhs, cploc), (rhs, cnloc));
    env = (env, []) }

let subtype_cons env ~neg ~pos (cp,cploc) (cn,cnloc) =
  let wrap_err k err =
    let wrap_cons c inner =
      let f k' _ = if Cons1.equal_field k k' then inner else Tsimple () in
      Cons1.mapi c ~neg:f ~pos:f
    in
    let tl, tr =
      if Cons1.field_is_positive k
      then err.lhs, err.rhs
      else err.rhs, err.lhs
    in
    { err with
      lhs = Tcons (wrap_cons cp tl, cploc);
      rhs = Tcons (wrap_cons cn tr, cnloc) }
  in
  let cp' =
    match Cons1.sub_head cp cn with
    | Un err -> raise (SubtypeError (make_err env (Head err) (cp,cploc) (cn,cnloc)))
    | Le coe -> Cons1.coerce_up coe cp
  in
  match
    Cons1.sub cp' cn
      ~neg:(fun k a b ->
        try neg a b
        with SubtypeError err -> raise (SubtypeError (wrap_err k err)))
      ~pos:(fun k a b ->
        try pos a b
        with SubtypeError err -> raise (SubtypeError (wrap_err k err)))
  with
  | Ok () -> ()
  | Error err -> raise (SubtypeError (make_err env (Sub err) (cp,cploc) (cn,cnloc)))

let lower_contains_fv fv lower =
  List.exists (function
    | Lflexvar a -> equal_flexvar a fv
    | Lcons (Top, _) -> true
    | _ -> false) lower

let lower_of_rigid_bound env rv : lower =
  env_rigid_bound env rv
  |> List.map (fun c -> Lcons (c,rv.loc))

(* Check whether a flex-flex constraint α ≤ β is already present via an upper bound of α *)
let rec has_flex_upper (pv : flexvar) nv =
  pv == nv ||
  match pv.upper with
  | Uflexvar pv' -> has_flex_upper pv' nv
  | Ugen {cons=_; higher_fvs} -> List.memq nv higher_fvs
  | Utop -> false

let upper_cons_map ~neg ~pos ((u,ul) : _ upper_cons Location.loc) : _ upper_cons Location.loc =
  u |> List.map (function
    | Urigvar _ as p -> p
    | Ucons c -> Ucons (Cons1.map ~neg ~pos c)),
  ul

let upper_find_cons cp (cn : _ upper_cons) =
  match
    cn
    |> List.filter_map (function
       | Urigvar _ -> None
       | Ucons cn ->
          match Cons1.sub_head cp cn with
          | Le hc -> Some (Either.Left (hc, cn))
          | Un r -> Some (Either.Right r))
    |> List.partition_map Fun.id
  with
  | (_ :: _ :: _), _ ->
     intfail "multiple compat cons in upper_cons"
  | [hc, cn], _ ->
     Ok (hc, cn)
  | _, errs ->
     Error (Cons1.merge_head_conflicts errs)

let upper_find_rv rv (cn : _ upper_cons) =
  match
    cn
    |> List.filter_map (function
      | Urigvar (rv', ds) when equal_rigvar rv rv' -> Some ds
      | _ -> None)
  with
  | _ :: _ :: _ -> intfail "duplicate RV in upper_cons"
  | [ds] -> Ok ds
  | [] -> Error ()

let upper_cons_is_top (cn : _ upper_cons) =
  match cn with
  | [Ucons Top] -> true
  | _ -> false

let rec match_sub ~changes env (p : lower_part) ((cn : (lower, lower_part list ref) upper_cons), cnloc) : unit =
  if upper_cons_is_top cn then ()
  else match p with
  | Lrigvar rv ->
     begin try
       match upper_find_rv rv cn with
       | Ok ds -> resolve_delayed_constraints ~changes env ds
       | Error () ->
          lower_of_rigid_bound env rv
          |> List.iter (fun l -> match_sub ~changes env l (cn, cnloc))
     with SubtypeError err ->
       (* FIXME update locations? Use rv.loc? *)
       let lhs = Tvar (Vrigid rv) in
       let (_l, lloc), (r, rloc) = err.located in
       let located = (lhs, lloc), (r, rloc) in
       raise (SubtypeError {err with lhs; located})
     end
  | Lcons (cp, cploc) ->
     begin match upper_find_cons cp cn with
     | Ok (_hc, cn) ->
        (* FIXME: use hc instead of recomputing? *)
        subtype_cons env (cp,cploc) (cn,cnloc)
          ~neg:(fun p n -> subtype_lu ~changes env p (Uflexvar n))
          ~pos:(fun p pr -> pr := !pr @ p)
     | Error errs ->
        raise (SubtypeError (make_err_nocons env errs (cp, cploc) (cn, cnloc)))
     end

  | Lflexvar pv ->
     let (upper, upper_loc), higher_fvs = rotate_flex ~changes env pv in
     (* shallow scope check *)
     let upper_in_scope = function
       | Urigvar (rv, _) -> Env_level.extends rv.level pv.level
       | Ucons _ -> true
     in
     let cn = List.filter upper_in_scope cn in
     let open struct
       type meet_pair =
         Meet_cons of
           { cons_a: (lower, flexvar) Cons1.t;
             cons_b: (lower, lower ref) Cons1.t;
             coe: (Cons1.head_coercion, Cons1.head_coercion) Either.t }
       | Meet_rv of
           { rigvar: rigvar;
             delay: delayed_constraint list }
     end in
     let meets_a =
       upper |> List.concat_map (function
         | Urigvar (rv, delay_a) ->
            begin match upper_find_rv rv cn with
            | Ok delay_b ->
               [Meet_rv { rigvar = rv; delay = delay_a @ delay_b }]
            | Error () ->
               (* rv included in output
                  iff up(rv) <= cn *)
               (* FIXME broken *)
               let d =
                 { dy_lower = lower_of_rigid_bound env rv;
                   dy_upper = Utop (*FIXME *);
                   dy_flexvar = pv;
                   dy_resolved = false }
               in
               [Meet_rv {rigvar = rv; delay = delay_a @ [d] }]
            end
         | Ucons cons_a ->
            begin match upper_find_cons cons_a cn with
            | Ok (coe, cons_b) ->
               [Meet_cons {cons_a; cons_b; coe=Left coe}]
            | Error _ -> []
            end)
     in
     let found_new_rv = ref false in
     let cons_decreased = ref false in
     let meets_b =
       cn |> List.concat_map (function
         | Urigvar (rv, delay_b) ->
            begin match upper_find_rv rv upper with
            | Ok _delay_a -> [] (* already in meets_a *)
            | Error () ->
               assert (Env_level.extends rv.level pv.level);
               (* FIXME improve check (subtype_cons at least) *)
               (* FIXME is this right? *)
(*               Format.printf "DELAY %a (upper %a / %a) on %a@." pp_ptyp (Tvar (Vrigid rv)) pp_upper (Ugen {cons=(upper,upper_loc);higher_fvs}) pp_upper pv.upper dump_ptyp (Tsimple (of_flexvar pv));*)
               let d =
                 { dy_lower = lower_of_rigid_bound env rv;
                   dy_upper = Ugen {cons=(upper,upper_loc);higher_fvs};
                   dy_flexvar = pv;
                   dy_resolved = false }
               in
               found_new_rv := true;
               [Meet_rv {rigvar=rv; delay = delay_b @ [d]}]
            end
         | Ucons cons_b ->
            begin match upper_find_cons cons_b upper with
            | Ok (Id, _) -> [] (* already in meets_a *)
            | Ok (coe, cons_a) ->
               cons_decreased := true;
               [Meet_cons {cons_a; cons_b; coe=Right coe}]
            | Error _ -> []
            end)
     in
     let upper =
       (meets_a @ meets_b)
       |> List.map (function
         | Meet_cons {cons_a; cons_b; coe} ->
            ignore coe; (* FIXME: pass this to meet to avoid recomputing? *)
            (* cons_a assumed already matchable, cons_b must be freshened *)
            let cons_a =
              if not !found_new_rv then cons_a
              else
                (* New rigvars means matchable variables must be re-freshened *)
                Cons1.map cons_a
                  ~neg:(fun x -> join_lower ~changes env pv.level bottom x)
                  ~pos:(fun x -> let v = fresh_flexvar pv.level in noerror (fun () -> subtype_flex_flex ~changes env v x); v)
            in
            let open One_or_two in
            let cons =
              Cons1.meet cons_a cons_b
                ~neg:(function
                  | L x -> x
                  | R r -> join_lower ~changes env pv.level bottom r
                  | LR (x, r) -> join_lower ~changes env pv.level x r)
                ~pos:(function
                  | L x -> x
                  | R r ->
                     let v = fresh_flexvar pv.level in
                     r := Lflexvar v :: !r;
                     v
                  | LR (v, r) ->
                     r := Lflexvar v :: !r;
                     v)
            in
            Ucons cons
         | Meet_rv {rigvar; delay} ->
            Urigvar (rigvar, delay))
     in
     (* Format.printf "MSUB %a@." dump_ptyp (Tsimple (of_flexvar pv)); *)
     (* FIXME: better fixpoint check here *)
     wf_ntyp env (Tsimple pv);
     let new_cons_loc =
       if !cons_decreased || upper_loc == Location.noloc then cnloc else upper_loc
     in
     let newbound = Ugen {cons = (upper, new_cons_loc); higher_fvs} in
     if fv_maybe_set_upper ~changes pv newbound then
       subtype_lu ~changes env pv.lower newbound;
     wf_ntyp env (Tsimple pv);
     ()

and resolve_delayed_constraints ~changes env ds =
  (* FIXME: where should the errors go from here? *)
  ds |> List.iter (fun dy ->
    (* FIXME: when are these resolved for flexvars going out of scope? *)
    assert (Env_level.extends dy.dy_flexvar.level (env_level env));
    (* FIXME: is recursion ever relevant here? *)
    if not dy.dy_resolved then begin
      dy.dy_resolved <- true;
      try
        subtype_lu ~changes env dy.dy_lower dy.dy_upper
      with
      | e ->     (*Format.printf "DELAYFAIL %a <= %a\n" pp_ptyp (Tsimple dy.dy_lower) pp_upper dy.dy_upper;*)  raise e

    end)

and subtype_lpu ~changes env (p : lower_part) (n : upper) =
  match n with
  | Utop -> ()
  | Ugen {cons=cn; higher_fvs} ->
     higher_fvs |> List.iter (fun nv -> subtype_lpu ~changes env p (Uflexvar nv));
     let constraints = ref [] in
     let templ = upper_cons_map cn ~neg:id ~pos:(fun t ->
       let r = ref [] in
       constraints := (r, t) :: !constraints;
       r)
     in
     match_sub ~changes env p templ;
     !constraints |> List.rev |> List.iter (fun (r, n) ->
       !r |> List.iter (fun p -> subtype_lpu ~changes env p (Uflexvar n)));
  | Uflexvar nv ->
     begin match p with
     | Lflexvar pv -> subtype_flex_flex ~changes env pv nv
     | p ->
        let lower = join_lower_part ~changes env nv.level nv.lower p in
        if fv_maybe_set_lower ~changes nv lower then
          subtype_lpu ~changes env p nv.upper
     end

and subtype_lu ~changes env (p : lower) (n : upper) =
  p |> List.iter (fun p -> subtype_lpu ~changes env p n)

and rotate_flex ~changes env (pv : flexvar) =
  match pv.upper with
  | Ugen {cons;higher_fvs} -> cons, higher_fvs
  | Utop ->
     let cons, higher_fvs = ([Ucons Top], Location.noloc), [] in
     fv_set_upper ~changes pv (Ugen {cons; higher_fvs});
     assert (equal_upper pv.upper (Ugen {cons; higher_fvs}));
     cons, higher_fvs
  | Uflexvar v' when Env_level.equal v'.level pv.level ->
     let cons, higher_fvs = ([Ucons Top], Location.noloc), [] in
     fv_set_upper ~changes pv (Ugen {cons; higher_fvs});
     noerror (fun () -> subtype_flex_flex ~changes env pv v'); (*FIXME: impl directly?*)
     (* upper may have changed, retry *)
     rotate_flex ~changes env pv
  | Uflexvar v' ->
     let cons, higher_fvs = ([Ucons Top], Location.noloc), [v'] in
     fv_set_upper ~changes pv (Ugen {cons; higher_fvs});
     assert (equal_upper pv.upper (Ugen {cons; higher_fvs}));
     cons, higher_fvs

and subtype_flex_flex ~changes env pv nv =
  (* We can record pv <= nv either as an upper bound on pv or a lower bound on nv.
     If they are not at the same level, our choice is forced.
     Otherwise, make an upper bound on pv, unless that would:
       - give pv two upper bounds, or
       - create a cycle of upper bounds *)
  if has_flex_upper pv nv || lower_contains_fv pv nv.lower then ()
  else if Env_level.extends nv.level pv.level
     && not (has_flex_upper nv pv) (* avoid creating cycles *)
     && pv.upper = Utop then begin
    fv_set_upper ~changes pv (Uflexvar nv);
    subtype_lu ~changes env pv.lower (Uflexvar nv)
  end else begin
    let pv_cons, pv_higher_fvs = rotate_flex ~changes env pv in
    if Env_level.extends pv.level nv.level then begin
      fv_set_lower ~changes nv (join_lower_part ~changes env nv.level nv.lower (Lflexvar pv));
      subtype_lu ~changes env (of_flexvar pv) nv.upper
    end else begin
      fv_set_upper ~changes pv (Ugen {cons=pv_cons; higher_fvs = nv::pv_higher_fvs});
      subtype_lu ~changes env pv.lower (Uflexvar nv)
    end
  end

and join_lower_part ~changes env level lower ty =
  let rec join_fv lower fv =
    match lower with
    | Lcons (Top, _) :: _ -> lower
    | Lflexvar fv' :: rest when equal_flexvar fv fv'
      (* alt: [has_flex_upper fv' fv] - is this better? *) ->
       Lflexvar fv :: rest
    | part :: rest -> part :: join_fv rest fv
    | [] ->
       let fv =
         if Env_level.extends fv.level level then fv
         else
           let fv' = fresh_flexvar level in
           noerror (fun () -> subtype_flex_flex ~changes env fv fv'); fv'
       in
       [Lflexvar fv]
  in
  let rec join_rv lower rv =
    match lower with
    | Lcons (Top, _) :: _ -> lower
    | Lrigvar rv' :: _ when equal_rigvar rv rv' -> lower
    | part :: rest -> part :: join_rv rest rv
    | [] ->
       assert (Env_level.extends rv.level level);
       [Lrigvar rv]
  in
  let join1 (ca, caloc) (cb, _cbloc) = (* ca assumed matchable & correct level *)
    let neg vl vr =
      noerror (fun () -> subtype_flex_flex ~changes env vl vr);
      vl
    in
    let pos a b = join_lower ~changes env level a b in
    Cons1.join ~neg ~pos ca cb, caloc (* FIXME loc *)
  in
  let rec join_cons lower ca_acc cb cb_loc =
    match lower with
    | (Lflexvar _ | Lrigvar _) as part :: rest -> part :: join_cons rest ca_acc cb cb_loc
    | Lcons (ca, ca_loc) as part :: rest ->
       begin match Cons1.sub_head cb ca with
       | Le hc -> (* cb <= ca, only once because antichain *)
          Lcons (join1 (ca, ca_loc) (Cons1.coerce_up hc cb, cb_loc)) :: rest
       | Un _ ->
          match Cons1.sub_head ca cb with
          | Le hc -> (* ca <= cb *)
             join_cons rest ((Cons1.coerce_up hc ca, ca_loc) :: ca_acc) cb cb_loc
          | Un _ ->
             part :: join_cons rest ca_acc cb cb_loc
       end
    | [] ->
       (* Must make cb matchable & at correct level *)
       let cons =
         Cons1.map cb
           ~neg:(fun v -> let v' = fresh_flexvar level in noerror (fun () -> subtype_flex_flex ~changes env v' v); v')
           ~pos:(fun l -> join_lower ~changes env level bottom l),
         cb_loc
       in
       let cons = List.fold_left (fun acc ca -> join1 ca acc) cons ca_acc in
       [Lcons cons]
  in
  match ty with
  | Lflexvar fv -> join_fv lower fv
  | Lrigvar rv ->
     if Env_level.extends rv.level level
     then join_rv lower rv
     else join_lower ~changes env level lower (lower_of_rigid_bound env rv)
  | Lcons (cb, cbloc) -> join_cons lower [] cb cbloc

and join_lower ~changes env level lower (ty : lower) =
  List.fold_left (join_lower_part ~changes env level) lower ty

let join_simple env a b =
  (* FIXME: start with a not bottom. (Improve matchability) *)
  let changes = ref [] in
  let r = bottom in
  let r = join_lower ~changes env (env_level env) r a in
  let r = join_lower ~changes env (env_level env) r b in
  r

let check_simple t =
  (* FIXME Tjoin / Tcons *)
  let rec aux = function
    | Tsimple _ | Tbot _ | Tvar _ -> ()
    | Tjoin _ -> () (* by invariant *)
    | Tpoly _ -> raise Exit
    | Tcons (c, _cloc) ->
       Cons1.map ~neg:aux ~pos:aux c |> ignore
  in
  match aux t with
  | () -> true
  | exception Exit -> false

let upper_is_bot = function
  | Ugen {cons=([],_); higher_fvs=_} -> true
  | _ -> false

let rec instantiate_flex env vars body =
  let fvars = IArray.map (fun _ -> fresh_flexvar (env_level env)) vars in
  let fvneg _loc i = Tsimple (IArray.get fvars i) in
  let fvpos _loc i = Tsimple (of_flexvar (IArray.get fvars i)) in
  IArray.iter2 (fun (fv : flexvar) (_,t) ->
    let b =
      match t with
      | None -> Utop
      | Some t -> ntyp_to_upper ~simple:true env (open_typ ~neg:fvpos ~pos:fvneg 0 t) in
    assert (fv.upper = Utop && is_bottom fv.lower);
    (* b need not be matchable, so we need to subtype_lpu rather
       than using it directly as fv.upper *)
    subtype_lpu ~changes:(ref []) env (Lflexvar fv) b)
    fvars vars;
  open_typ ~neg:fvneg ~pos:fvpos 0 body

and ptyp_to_lower ~simple env : ptyp -> lower = function
  | Tsimple t -> t
  | Tbot _loc -> [] (*FIXME: loc?*)
  | Tcons (cons, loc) ->
     let cons = Cons1.map ~neg:(ntyp_to_flexvar ~simple env) ~pos:(ptyp_to_lower ~simple env) cons in
     [Lcons (cons, loc)]
  | Tvar (Vbound _) -> intfail "Vbound"
  | Tvar (Vrigid rv) -> of_rigvar rv
  | Tjoin (a, b, _loc) -> join_simple env (ptyp_to_lower ~simple:true env a) (ptyp_to_lower ~simple:true env b)
  | Tpoly {vars; body} ->
     assert (not simple);
     let body = instantiate_flex env vars body in
     ptyp_to_lower ~simple env body

(* Result is not necessarily matchable, so cannot be used directly as fv.upper *)
and ntyp_to_upper ~simple env : ntyp -> upper = function
  | Tsimple t -> Uflexvar t
  | Tcons (Top, _) -> Utop
  | Tbot loc ->
     Ugen {cons = ([], Option.value loc ~default:Location.(fixme "ntyp_Tbot")); higher_fvs = []}
  | Tcons (cons, consloc) ->
     let cons = Cons1.map ~neg:(ptyp_to_lower ~simple env) ~pos:(ntyp_to_flexvar ~simple env) cons in
     Ugen {cons = ([Ucons cons], consloc); higher_fvs = []}
  | Tvar (Vbound _) -> intfail "Vbound"
  | Tvar (Vrigid rv) ->
     Ugen {cons = ([Urigvar (rv, [])], rv.loc); higher_fvs = []}
  | Tjoin (a, b, jloc) as ty ->
     begin match
       ntyp_to_upper ~simple:true env a, ntyp_to_upper ~simple:true env b
     with
     | Uflexvar _, _ | _, Uflexvar _ -> intfail "join of flexvar negatively: %a" pp_ntyp ty
     | Utop, _ | _, Utop -> Utop
     | Ugen c1, Ugen c2 ->
        let cons =
          match c1.cons, c2.cons with
          | (c1, loc1), (c2, _loc2) ->
             let loc = Option.value jloc ~default:loc1 in
             (c1 @ c2, loc)
        in
        Ugen { cons; higher_fvs = c1.higher_fvs @ c2.higher_fvs }
     end
  | Tpoly {vars; body} ->
     assert (not simple);
     (* Negative var occurrences should be replaced with their upper
        bounds, positive ones should be deleted. *)
     let bounds = Array.make (IArray.length vars) None in
     let neg _l v =
       match bounds.(v) with
       | None -> intfail "recursive rigid bound"
       | Some t -> Tsimple t in
     let pos l _v = Tbot (Some l) in
     vars |> IArray.iteri (fun i (_, b) ->
       let b = Option.map (open_typ ~neg:pos ~pos:neg 0) b in
       let b = Option.map (ptyp_to_lower ~simple:true env) b in
       bounds.(i) <- b);
     let body = open_typ ~neg ~pos 0 body in
     ntyp_to_upper ~simple env body

and ntyp_to_flexvar ~simple env (t : ntyp) =
  match ntyp_to_upper ~simple env t with
  | Utop -> fresh_flexvar (env_level env)
  | Uflexvar v -> v
  | Ugen _ as u ->
     let fv = fresh_flexvar (env_level env) in
     noerror (fun () -> subtype_lu ~changes:(ref []) env (of_flexvar fv) u);
     fv

(*
 * Subtyping on typs (polymorphism)
 *)

let enter_rigid env vars rig_names =
  let level = Env_level.extend (env_level env) in
  let temp_env =
    Env_types { level; rig_names;
                rig_defns = IArray.map (fun (name, _) ->
                    {name; upper=[Top]}) vars; rest = env } in
  let getrv loc var = Tvar (Vrigid {level; loc; var}) in
  let openrig t = open_typ ~neg:getrv ~pos:getrv 0 t in
  let rig_defns = IArray.map (fun (name, b) ->
     let upper =
       match b with
       | None -> [Lcons (Top, snd name)]
       | Some b -> ptyp_to_lower ~simple:true temp_env (openrig b) in
     match upper with
     | [Lcons (Top, _)] ->
        { name; upper = [Top] }
     | lower ->
       (* FIXME: can you actually hit this?
          Try with a higher-rank type where the outer rank gets instantiated.
          Maybe change the type of the upper bound in parsed types.
          (to reflect its Tconsness)*)
        let conses = lower |> List.map (function
          | Lcons (c,_) -> c
          | Lrigvar _ | Lflexvar _ -> assert false)
        in
        { name; upper = conses }) vars in
  let env = Env_types { level; rig_names; rig_defns; rest = env} in
  env, openrig

let rec subtype env (p : ptyp) (n : ntyp) =
  (* Format.printf "%a <= %a\n" dump_ptyp p pp_ntyp n; *)
  wf_ptyp env p; wf_ntyp env n;
  match p, n with
  | _, Tcons (Top, _) -> ()
  | Tbot _, _ -> ()
  | Tcons cp, Tcons cn ->
     subtype_cons env ~neg:(subtype env) ~pos:(subtype env) cp cn
  | p, Tpoly {vars; body} ->
     let orig_env = env in
     let env, open_rvars = enter_rigid env vars SymMap.empty in
     let body = open_rvars body in
     (try subtype env p body
      with SubtypeError err ->
        raise (SubtypeError (close_err_rigid ~orig_env ~env vars err)))
  | Tpoly {vars; body}, n ->
     let body = instantiate_flex env vars body in
     subtype env body n; ()
  | p, ((Tsimple _ | Tvar _ | Tjoin _ | Tcons _ | Tbot _) as n) ->
     let u = ntyp_to_upper ~simple:false env n in
     subtype_lu ~changes:(ref []) env (ptyp_to_lower ~simple:false env p) u;
     wf_ptyp env p; wf_ntyp env n;
     ()

let subtype env p n =
  (* FIXME: revert changes on failure? *)
  match subtype env p n with
  | exception SubtypeError e ->
     assert (fst e.env == env);
     Error e
  | () -> Ok ()

(* FIXME: rank1 joins maybe?
   FIXME: keep types as Tcons if possible? Better inference. Can this matter? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  match p, q with
  | Tbot _, x | x, Tbot _ -> x
  | p, q ->
     Tsimple (join_simple env (ptyp_to_lower ~simple:false env p) (ptyp_to_lower ~simple:false env q))

(* FIXME: is this ever needed in nontrivial ways? *)
let meet_ntyp env (p : ntyp) (q : ntyp) : ntyp =
  match p, q with
  | Tcons (Top, _), x | x, Tcons (Top, _) -> x
  | p, q ->
     let v = fresh_flexvar (env_level env) in
     subtype_lu ~changes:(ref []) env (of_flexvar v) (ntyp_to_upper ~simple:false env p);
     subtype_lu ~changes:(ref []) env (of_flexvar v) (ntyp_to_upper ~simple:false env q);
     Tsimple v

let rec match_ptyp ~loc env (p : ptyp) (heads : (ntyp ref, ptyp ref) upper_cons) =
  match p with
  | Tcons (c, cloc) ->
     begin match upper_find_cons c heads with
     | Ok (_hc, head) ->
        subtype_cons env (c, cloc) (head, loc)
          ~neg:(fun v t -> v := meet_ntyp env !v t)
          ~pos:(fun t v -> v := join_ptyp env !v t)
     | Error err ->
        raise (SubtypeError (make_err_nocons env err (c, cloc) (heads, loc)))
     end
  | Tjoin (a, b, _) ->
     match_ptyp ~loc env a heads; match_ptyp ~loc env b heads
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_ptyp ~loc env body heads
  | t ->
     let instneg v =
       let fv = fresh_flexvar (env_level env) in
       v := meet_ntyp env !v (Tsimple fv);
       of_flexvar fv in
     let ref_pairs = ref [] in
     let shead = upper_cons_map ~neg:instneg ~pos:(fun v -> let r = ref [] in ref_pairs := (v,r) :: !ref_pairs; r) (heads,loc) in
     ptyp_to_lower ~simple:false env t
     |> List.iter (fun l ->
       match_sub ~changes:(ref []) env l shead);
     !ref_pairs |> List.iter (fun (v, r) -> v := join_ptyp env !v (Tsimple !r))

let match_ptyp ~loc env ty heads =
  let heads = List.map (fun x -> Ucons x) heads in
  match match_ptyp ~loc env ty heads with
  | () -> Ok ()
  | exception (SubtypeError e) ->
     assert (fst e.env == env);
     Error e

(*
 * Generalisation
 *)

(* Returns true only if a <= b
   Not complete, never changes anything.
   Used only for optimisations, to avoid generalising a when x <= a <= x.
   Not a bug if it spuriously returns false sometimes (but leads to uglier types) *)
(* FIXME: can this diverge? *)
let rec clearly_subtype env (a : flexvar) (b : lower) : bool =
  lower_contains_fv a b ||
  match a.upper with
  | Utop -> false
  | Uflexvar a -> clearly_subtype env a b
  | Ugen {cons=(cn,cnloc); higher_fvs} ->
    List.exists (fun a' -> clearly_subtype env a' b) higher_fvs ||
    cn |> List.for_all (fun u ->
      b |> List.exists (fun l ->
        match u, l with
        | Urigvar (rv, []), Lrigvar rv' -> equal_rigvar rv rv'
        | Ucons cn, Lcons cp ->
           let sub a b = if not (clearly_subtype env a b) then raise Exit in
           begin match subtype_cons env ~neg:sub ~pos:sub (cn,cnloc) cp with
           | exception (SubtypeError _ | Exit) -> false
           | () -> true
           end
        | _ -> false))

(* This function could be optimised by skipping subtrees that have no use
   of the outermost level, Remy-style *)
let rec map_typ_simple : 'neg1 'pos1 'neg2 'pos2 .
  neg:(index:int -> ('pos1,'neg1) typ -> ('pos2, 'neg2) typ) ->
  pos:(index:int -> ('neg1,'pos1) typ -> ('neg2, 'pos2) typ) ->
  index:int -> ('neg1, 'pos1) typ -> ('neg2, 'pos2) typ =
  fun ~neg ~pos ~index -> function
  | Tbot _ as t -> t
  | Tcons (c, cloc) ->
     Tcons (Cons1.map
              ~neg:(map_typ_simple ~pos:neg ~neg:pos ~index)
              ~pos:(map_typ_simple ~neg ~pos ~index)
              c,
            cloc)
  | Tjoin (a, b, jloc) ->
     Tjoin(map_typ_simple ~neg ~pos ~index a, map_typ_simple ~neg ~pos ~index b, jloc)
  | Tvar (Vbound _) as t -> t
  | Tsimple _
  | Tvar (Vrigid _) as t ->
     pos ~index t
  | Tpoly {vars; body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (n, t) -> n, Option.map (map_typ_simple ~neg:pos ~pos:neg ~index) t) vars in
     let body = map_typ_simple ~neg ~pos ~index body in
     Tpoly {vars; body}

(* FIXME: bit weird... There must be a better representation for bvars here *)

type genvar =
  | Gen_flex of ntyp
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

(* Invariants after expansion:
   - All flexvars are joined with their lower bounds
   - All +-reachable flexvars are rotated
   - All --reachable flexvars have at most one upper bound
      (not counting UBvar upper bounds at higher levels)
   (Only applied to flexvars at the current level) *)

let remove_flexvar fv lower =
  List.filter (function Lflexvar a when equal_flexvar fv a -> false | _ -> true) lower

let rec expand_lower visit ~changes ?(vexpand=[]) env orig_lower =
  let level = env_level env in
  let lower =
    orig_lower |> List.map (function
      | Lflexvar pv when Env_level.equal pv.level level ->
          fv_gen_visit_pos env visit pv (function
            | Recursive_visit ->
               (* recursive occurrences are fine if not under a constructor *)
               if not (List.memq pv vexpand)
               then unimp "positive recursion on flexvars"
            | First_visit ->
               let _, _ = rotate_flex ~changes env pv in
               (* Add pv to expand so we ignore it if seen before the next ctor *)
               let lower = expand_lower visit ~changes ~vexpand:(pv::vexpand) env pv.lower in
               ignore (fv_maybe_set_lower ~changes pv (remove_flexvar pv lower)));
          Lflexvar pv
      | Lflexvar _ | Lrigvar _ as l -> l
      | Lcons (c, cloc) ->
         Lcons (Cons1.map c ~neg:(expand_fv_neg visit ~changes env) ~pos:(expand_lower visit ~changes env), cloc))
  in
  let lower =
    List.fold_left
      (fun acc l ->
        match l with
        | Lflexvar fv when Env_level.equal fv.level level ->
           join_lower ~changes env level acc fv.lower
        | _ -> acc)
      lower
      lower
  in
  let lower_rest, fv_here =
    lower |> List.partition_map (function
      | Lflexvar fv when Env_level.equal fv.level level -> Right fv
      | l -> Left l)
  in
  let fv_here =
    fv_here
    |> List.filter (fun fv -> not (clearly_subtype env fv lower_rest))
    |> List.map (fun x -> Lflexvar x)
  in
  lower_rest @ fv_here


and expand_fv_neg visit ~changes env nv =
  fv_gen_visit_neg env visit nv (function
    | Recursive_visit ->
       unimp "neg cycle on recursive flexvar"
    | First_visit ->
       match nv.upper with
       | Utop -> ()
       | Uflexvar v when Env_level.equal nv.level v.level ->
          ignore (expand_fv_neg visit ~changes env v)
       | _ ->
          let cons, higher_fvs = rotate_flex ~changes env nv in
             let change = ref false in
             let cons =
               upper_cons_map cons
                 ~neg:(fun x -> let x' = expand_lower visit ~changes env x in
                                if not (equal_lower x x') then change := true;
                                x')
                 ~pos:(expand_fv_neg visit ~changes env)
             in
             (* FIXME change tracking *)
             if true || !change then ignore (fv_maybe_set_upper ~changes nv (Ugen {cons=cons; higher_fvs}))
  );
  nv

(* FIXME: does not yet detect the creation of contravariant joins
   during promotion. These arise (only?) during promotions with
   rigvars at the current level. *)

type ('n, 'p) promotion_policy =
  | Policy_hoist : env -> (flexvar, lower) promotion_policy
  | Policy_generalise : Location.t -> (zero, zero) promotion_policy

type ('n, 'p) promote_info = {
  visit: int;
  bvars: genvar Vector.t;
  env: env;
  level: Env_level.t;
  index: int;
  mode: [`Poly | `Elab];
  policy : ('n, 'p) promotion_policy;
}


let promote_rigvar s (rv : rigvar) =
  if Env_level.equal rv.level s.level
  then ((match Vector.get s.bvars rv.var with Gen_rigid r -> assert (equal_rigvar rv r) | _ -> assert false);
        Vbound {index=s.index; var=rv.var; loc=rv.loc})
  else Vrigid rv

type ('n, 'p) promote_flexvar_result =
  | Generalised : int -> (zero, zero) promote_flexvar_result
  | Hoisted : flexvar -> (flexvar, lower) promote_flexvar_result

let rec promote_lower :
  type n p . (n, p) promote_info -> lower -> (n, p) typ =
  fun s lower ->
  lower
  |> List.filter_map (function
    | Lcons (c,cloc) ->
       Some ((0,0), tcons (Cons1.map ~neg:(promote_fv_neg s) ~pos:(promote_lower s) c, cloc))
    | Lrigvar rv ->
       let v = promote_rigvar s rv in
       let k = match v with Vrigid rv -> (1, rv.var) | Vbound v -> (2, v.var) in
       Some (k,Tvar v)
    | Lflexvar fv ->
       match promote_flexvar s fv with
       | None -> None
       | Some r ->
          match s.policy with
          | Policy_generalise loc ->
             let Generalised var = r in
             Some ((2,var),Tvar (Vbound {index=s.index; var; loc}))
          | Policy_hoist _env ->
             let Hoisted fv = r in
             Some ((2,0),Tsimple [Lflexvar fv]))
  |> List.sort (fun (ka,_) (kb,_) -> compare ka kb)
  |> List.map snd
  |> tjoin'

and promote_fv_neg :
  type n p . (n, p) promote_info -> flexvar -> (p, n) typ =
  fun s nv ->
  match promote_flexvar s nv, s.policy with
  | None, _ ->
     (* substitute away the variable *)
     let vars, ty = promote_upper s nv in
     assert (vars = []);
     ty
  | Some (Generalised var), Policy_generalise loc ->
     let v = Vbound {index=s.index; var; loc} in
     assert (is_visited_pos s.visit nv);
     begin match s.mode with
     | `Poly -> Tvar v
     | `Elab ->
        (* Here a positive type is used as negative, but only when:
           - Elab, so placement of rigid variables doesn't matter
           - Policy_generalise, so there are no flexible variables *)
        tvjoin ~base:(promote_lower s nv.lower) [v]
     end
  | Some (Hoisted v), Policy_hoist hoist_env ->
     assert (Env_level.extends v.level (env_level hoist_env));
     Tsimple v

and promote_upper :
  type n p . (n, p) promote_info -> flexvar -> flexvar list * (p,n) typ =
  fun s fv ->
  match fv.upper with
  | Uflexvar v when Env_level.equal v.level s.level ->
     assert (not (is_visited_pos s.visit fv));
     [], promote_fv_neg s v
  | u ->
     let c, loc, vars =
       match u with
       | Utop -> [Ucons Top], Location.noloc, []
       | Uflexvar v -> [Ucons Top], Location.noloc, [v]
       | Ugen {cons=(c,loc); higher_fvs} -> c, loc, higher_fvs
     in
     let conses, rigvars = c |> List.partition_map (function
        | Urigvar (r,_ds) ->
           (*if List.exists (fun d -> not d.dy_resolved) ds then
             intfail "FIXME unresolved delayed constraints"; FIXME*)
           Either.Right (promote_rigvar s r)
        | Ucons c ->
           let c = Cons1.map ~neg:(promote_lower s) ~pos:(promote_fv_neg s) c in
           Either.Left (tcons (c,loc))) in
     let base = List.fold_left (tjoin ~loc) (Tbot (Some loc)) conses in
     (* FIXME: can this create contravariant joins? *)
     vars, tvjoin ~base rigvars


and promote_flexvar :
  type n p . (n, p) promote_info -> flexvar -> (n, p) promote_flexvar_result option =
  fun s fv ->
  if not (Env_level.equal fv.level s.level) then
    match s.policy with
    | Policy_hoist hoist_env ->
       assert (Env_level.extends fv.level (env_level hoist_env));
       Some (Hoisted fv)
    | Policy_generalise _ ->
       intfail "Flexible variable found during generalisation" (* MonoLocalBinds *)
  else begin
  assert (Env_level.equal fv.level s.level);
  match fv.gen with
  | Not_generalising -> assert false
  | Generalising gen ->
     let upper_requires_hoist = function
       | Uflexvar v when Env_level.equal v.level s.level -> false
       | Utop | Ugen {cons=_; higher_fvs=[]} -> false
       | _ -> true
     in
     if not (gen.visit.neg = s.visit && (gen.visit.pos = s.visit || upper_requires_hoist fv.upper))
     then None
     else match gen.bound_var with
     | Computing_bound ->
        (* FIXME: detect all recursion cases during expand so this can go away *)
        unimp "flexvar recursive in own bound"
     | Generalised var ->
        (match s.policy with Policy_generalise _ -> Some (Generalised var) | _ -> assert false)
     | Kept fv ->
        (match s.policy with Policy_hoist _ -> Some (Hoisted fv) | _ -> assert false)
     | Replace_with_rigid _ ->
        assert false
     | No_var_chosen ->
        gen.bound_var <- Computing_bound;
        let bv : flexvar_gen_status =
          assert (is_visited_pos s.visit fv || upper_requires_hoist fv.upper);
          let vars, upper = promote_upper s fv in
          match s.policy with
          | Policy_generalise _ ->
            assert (vars = []); (* since visited_pos *)
            let n = Vector.push s.bvars (Gen_flex (gen_zero upper)) in
            Generalised n
          | Policy_hoist hoist_env ->
              (* FIXME: surely I need to consider fv.lower as well? *)
            let h = fresh_flexvar (env_level hoist_env) in
            Result.get_ok
              (subtype hoist_env (Tsimple (of_flexvar h)) upper);
            vars |> List.iter (fun var' ->
              Result.get_ok
                (subtype hoist_env (Tsimple (of_flexvar h)) (Tsimple var')));
            Kept h
        in
        gen.bound_var <- bv;
        (* FIXME refactor *)
        promote_flexvar s fv
  end

let fixpoint_iters = ref 0
let log_changes = ref false
let verbose_types = match Sys.getenv "VERBOSE_TYPES" with _ -> true | exception Not_found -> false

let promote ~policy ~rigvars ~env ~(map : neg:_ -> pos:_ -> _ -> _) ty =
  (* Format.printf "ELAB %a{\n%a}@." dump_ptyp orig_ty pp_elab_req erq; *)
  let rec fixpoint visit prev_ty =
    (* if verbose_types then Format.printf "FIX: %a" dump_ptyp prev_ty; *)
    if visit > 99 then intfail "looping?";
    let changes = ref [] in
    let neg_simple ~index:_ t =
      let t = ntyp_to_flexvar ~simple:true env t in
      Tsimple (expand_fv_neg visit ~changes env t)
    in
    let pos_simple ~index:_ t =
      let t = ptyp_to_lower ~simple:true env t in
      let t' = expand_lower visit ~changes env t in
      if not (equal_lower t t') then
        changes := Change_expanded_mark :: !changes;
      Tsimple t'
    in
    let neg ~mode:_ ~index t = map_typ_simple ~neg:pos_simple ~pos:neg_simple ~index t in
    let pos ~mode:_ ~index t = map_typ_simple ~neg:neg_simple ~pos:pos_simple ~index t in
    let ty = map ~neg ~pos prev_ty in
    if !log_changes || visit > 90 then Format.printf "changed: %a\n\n%!" pp_changes !changes;
    if !changes = [] then
      (visit, ty)
    else
      (incr fixpoint_iters; fixpoint (visit+2) ty) in
  let visit, ty = fixpoint 2 ty in
  (* Format.printf "ELAB2 %a{\n%a}@." dump_ptyp ty pp_elab_req erq; *)
  let bvars = Vector.create () in
  rigvars |> IArray.iteri (fun var ((_,loc),_) -> ignore (Vector.push bvars (Gen_rigid {loc;var;level=env_level env})));
  let get_simple = function Tsimple t -> t | _ -> intfail "promote unexpanded?" in
  let promote (type p) (type n) (policy : (n,p) promotion_policy) =
    let s_base = { visit; bvars; env; level = env_level env; mode = `Poly; index = -1; policy } in
    let neg_simple ~mode ~index t : ntyp =
      let t = promote_fv_neg {s_base with mode; index} (get_simple t) in
      match policy with Policy_generalise _ -> gen_zero t | Policy_hoist _ -> t
    in
    let pos_simple ~mode ~index t : ptyp =
      let t = promote_lower {s_base with mode; index} (get_simple t) in
      match policy with Policy_generalise _ -> gen_zero t | Policy_hoist _ -> t
    in
    map ty
      ~neg:(fun ~mode ~index t ->
        map_typ_simple ~neg:(pos_simple ~mode) ~pos:(neg_simple ~mode) ~index t)
      ~pos:(fun ~mode ~index t ->
        map_typ_simple ~neg:(neg_simple ~mode) ~pos:(pos_simple ~mode) ~index t)
  in
  (* Format.printf "ELAB3 %a{\n%a}@." dump_ptyp ty pp_elab_req erq; *)
  let ty =
    match policy with
    | `Generalise loc -> promote (Policy_generalise loc)
    | `Hoist env -> promote (Policy_hoist env)
  in
  bvars, ty
