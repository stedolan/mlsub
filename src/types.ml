open Util
open Typedefs

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)


type mismatch = (unit, unit) typ * (unit, unit) typ
type subtyping_error = {
  lhs : (unit, unit) typ;
  rhs : (unit, unit) typ;
  err : Cons.subtype_error;
  env : env * string iarray list;
}
exception SubtypeError of subtyping_error

let close_err_rigid ~orig_env ~env vars {lhs; rhs; err; env = (_env', ext)} =
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
  let ext = IArray.map (fun ((s,_),_) -> s) vars :: ext in
  { lhs; rhs; err; env = (orig_env, ext) }

(* FIXME most uses are making fresh vars above/below something. Refactor? *)
let[@inline] noerror f = try f () with SubtypeError _ -> intfail "subtyping error should not be possible here!"

(*
 * Core subtyping functions
 *)

(* There are two ways to represent a constraint α ≤ β between two flexible variables.
   (I). Make the upper bound of α be UBvar β. (Ensure also that LB(β) contains LB(α))
   (II). Make the lower bound of β contain α. (Ensure also that UB(α) contains UB(β)) *)


let tjoin a b =
  match a, b with
  | Tcons c, x when Cons.is_bottom c -> x
  | x, Tcons c when Cons.is_bottom c -> x
  | a, b -> Tjoin (a, b)

let tvjoin ?(base=Tcons Cons.bottom) vs =
  List.fold_left (fun t (l,v) -> tjoin t (Tvar (l, v))) base vs

let tcons conses = Tcons conses

(* head ctors for errors *)
(* FIXME: maybe keep small subterms? (See Tsimple ())*)
let cons_head c = Tcons (Cons.map ~neg:(fun _ -> Tsimple ()) ~pos:(fun _ -> Tsimple ()) c)

let ctor_head {cons;rigvars} =
  tvjoin ~base:(cons_head cons) (List.map (fun (rv,l) -> l,Vrigid rv) (Rvset.to_list_loc rigvars))

let ctor_pick_loc {cons;rigvars} =
  match Cons.Locs.pick cons.locs, Rvset.to_list_loc rigvars with
  | Some (_, l), _ -> Some l
  | None, (_, l :: _) :: _ -> Some l
  | _ -> None

let subtype_conses env ~neg ~pos cp cn =
  match Cons.subtype cp cn.cons with
  | Error err ->
     let err =
       match err.located, Rvset.to_list_loc cn.rigvars with
       | None, (_, r :: _) :: _ ->
          (* FIXME [] *)
          {err with located = Some (([], Option.get (ctor_pick_loc {cons=cp;rigvars=Rvset.empty})), ([], r)) }
       | _ -> err
     in
     raise (SubtypeError {lhs=cons_head cp; rhs=ctor_head cn; err; env=(env,[])})
  | Ok subs ->
     let sub fn field a b =
       try fn a b
       with SubtypeError {lhs; rhs; err; env} ->
         let wrap outer inner =
           let neg k _x = if Cons.equal_field (F_neg k) field then inner else Tsimple () in
           let pos k _x = if Cons.equal_field (F_pos k) field then inner else Tsimple () in
           Tcons (Cons.mapi ~neg ~pos outer)
         in
         let err =
           match field with
           | F_pos _ -> {lhs = wrap cp lhs; rhs = wrap cn.cons rhs; err; env}
           | F_neg _ -> {lhs = wrap cp rhs; rhs = wrap cn.cons lhs; err; env}
         in
         raise (SubtypeError err)
     in
     subs |> List.iter (function
       | Cons.S_neg (f, (a, b)) -> sub neg (Cons.F_neg f) a b
       | Cons.S_pos (f, (a, b)) -> sub pos (Cons.F_pos f) a b)

(* add some flexvars to a join.
   does not check levels, so level of resulting join may increase *)
let join_flexvars lower vs =
  match lower with
  | Ltop l -> Ltop l
  | Lower (flex, ctor) ->
     Lower (Fvset.append flex vs ~merge:(fun a _ -> a), ctor)

let lower_contains_fv fv = function
  | Ltop _ -> true
  | Lower (flex, _) -> Fvset.mem fv flex

let lower_of_rigid_bound env (rv, rvloc) =
  match env_rigid_bound env rv with
  | None -> Ltop (Some (match rvloc with l :: _ -> l | [] -> snd (env_rigid_var env rv).name))
  | Some c -> Lower(Fvset.empty, {cons=c; rigvars=Rvset.empty})

(* Check whether a flex-flex constraint α ≤ β is already present via an upper bound of α *)
let rec has_flex_upper (pv : flexvar) nv =
  pv == nv || pv.upper |> List.exists (function
  | UBvar pv' -> has_flex_upper pv' nv
  | UBcons _ -> false)

let rec match_sub ~changes env (p : flex_lower_bound) (cn : (flex_lower_bound, flex_lower_bound ref) ctor_ty) : unit =
  match p with
  | Ltop loc ->
     let located =
       match loc, ctor_pick_loc cn with
       | Some l, Some r ->
          (* FIXME [] *)
          Some (([], l), ([], r))
       | _ -> None
     in
     raise (SubtypeError {lhs=Ttop loc; rhs=ctor_head cn; err={conflict=Incompatible; located}; env=(env,[])})
  | Lower(pflex, {cons; rigvars}) ->
     (* constructed type *)
     subtype_conses env cons cn
       ~neg:(fun p n -> subtype_lu ~changes env p (UBvar n))
       ~pos:(fun p r -> r := join_lower ~changes env (env_level env) !r p);
     (* rigid variables *)
     Rvset.to_list_loc rigvars
     |> List.filter (fun (rv, _loc) -> not (Rvset.contains cn.rigvars rv))
     |> List.iter (fun (rv, rvloc) ->
       try match_sub ~changes env (lower_of_rigid_bound env (rv, rvloc)) cn
       with SubtypeError err ->
         let lhs = Tvar (rvloc, Vrigid rv) in
         (* FIXME: update err.err as well? *)
         raise (SubtypeError {err with lhs}));
     (* flexible variables *)
     Fvset.iter pflex ~f:(fun pv ->
       let cn =
         match List.partition (fun ((rv:rigvar),_) -> Env_level.extends rv.level pv.level) (Rvset.to_list_loc cn.rigvars) with
         | _, [] -> cn
         | _rigvars, drop ->
            let drop =
              drop |> List.concat_map (function (_, l :: _) -> [[], l] | _ -> []) in
            { cons = { cn.cons with locs = Cons.Locs.append' cn.cons.locs drop ~merge:(fun a _ -> a) };
              rigvars = (*FIXME*) Rvset.filter (fun rv -> Env_level.extends rv.level pv.level) cn.rigvars }
       in
       let cbs_match, up_rest = List.partition (function UBvar _ -> false | UBcons cb -> Rvset.equal cn.rigvars cb.rigvars) pv.upper in
       let meet pvcons =
         let pvcons = Cons.meet pvcons cn.cons in
         let m ~neg ~pos = Cons.map ~neg ~pos pvcons in
         m
           ~neg:(function
             | L x -> x
             | R r -> join_lower ~changes env pv.level bottom r
             | LR (x, r) -> join_lower ~changes env pv.level x r)
           ~pos:(function
             | L x -> x
             | R r ->
                let v = fresh_flexvar pv.level in
                r := join_lower ~changes env (env_level env) !r (of_flexvar v);
                v
             | LR (v, r) ->
                r := join_lower ~changes env (env_level env) !r (of_flexvar v);
                v)
       in
       let cbnew, new_rvset, bound_is_new =
         match cbs_match with
         | [] ->
            let cons' = Cons.map ~neg:(fun _ -> bottom) ~pos:(fun _ -> fresh_flexvar pv.level) cn.cons in
            let m = meet cons' in
            m, true, true
         | [UBcons c] ->
            let m = meet c.cons in
            m, false,
            not (Cons.equal ~neg:equal_flex_lower_bound ~pos:equal_flexvar m c.cons)
         | _ -> intfail "duplicate bounds with same rigvar set" in
       if bound_is_new then begin
         let newbound = UBcons {rigvars=cn.rigvars; cons=cbnew} in
         fv_set_upper ~changes pv (newbound :: up_rest);
         rotate_flex ~changes env pv; (* improves sharing between match vars *)
         subtype_lu ~changes env pv.lower newbound;
         if new_rvset then ensure_rigvars_present ~changes env pv;
       end;
       subtype_conses env cbnew cn
         ~neg:(fun _ _ -> (* already done above *) ())
         ~pos:(fun p r -> r := join_lower ~changes env (env_level env) !r (of_flexvar p))
     )

and subtype_lu ~changes env (p : flex_lower_bound) (n : styp_neg) =
  match n with
  | UBcons cn ->
     let cntempl = Cons.map ~neg:id ~pos:(fun _ -> ref bottom) cn.cons in
     match_sub ~changes env p {cn with cons = cntempl};
     subtype_conses env cntempl cn
       ~neg:(fun _ _ -> ())
       ~pos:(fun p nv -> subtype_lu ~changes env !p (UBvar nv))

  | UBvar nv ->
     let p =
       match p with
       | Ltop _ -> p
       | Lower(fvs, cp) ->
          Fvset.iter fvs ~f:(fun pv -> subtype_flex_flex ~changes env pv nv);
          Lower(Fvset.empty, cp)
     in
     let lower = join_lower ~changes env nv.level nv.lower p in
     (* FIXME hoisting: is cp OK? shouldn't we compare against lower? Might that be different? *)
     if fv_maybe_set_lower ~changes nv lower then begin
       nv.upper |> List.iter (fun n -> subtype_lu ~changes env p n);
       ensure_rigvars_present ~changes env nv;
     end

(* Ensure every rigvar appearing in a flexvar's lower bounds also
   appears in its constructed upper bounds.
     rv <= a <= C implies rv <= a <= C | rv since rv <= C is C = C | rv *)
and ensure_rigvars_present ~changes env (fv : flexvar) =
  match fv.lower with
  | Ltop _ -> ()
  | Lower(_, {rigvars;_}) when Rvset.is_empty rigvars -> ()
  | Lower(_, {rigvars=rvlow; _}) ->
     let keep, recheck = fv.upper |> List.partition (function
       | UBvar _ -> true
       | UBcons {cons=_;rigvars} ->
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
            noerror (fun () -> subtype_lu ~changes env (of_flexvar fv) (UBcons cb)))

and rotate_flex ~changes env (pv : flexvar) =
  (* FIXME hoisting: do flexvars remain rotated if things hoist? *)
  if not pv.rotated then begin
    (* FIXME backtracking here (add to ~changes) *)
    pv.rotated <- true;
    let rotate, keep = pv.upper |> List.partition_map (function
       | UBvar v' when Env_level.equal v'.level pv.level -> Left v'
       | u -> Right u) in
    match rotate with
    | [] -> ()
    | rotate ->
       fv_set_upper ~changes pv keep;
       rotate |> List.iter (fun v' -> noerror (fun () -> subtype_flex_flex ~changes env pv v'))
  end
        
and subtype_flex_flex ~changes env pv nv =
  (* We can record pv <= nv either as an upper bound on pv or a lower bound on nv.
     If they are not at the same level, our choice is forced.
     Otherwise, make an upper bound on pv, unless that would:
       - give pv two upper bounds, or
       - create a cycle of upper bounds *)
  if has_flex_upper pv nv || lower_contains_fv pv nv.lower then ()
  else if Env_level.extends nv.level pv.level
     && not (has_flex_upper nv pv) (* avoid creating cycles *)
     && ((pv.upper = [] && not pv.rotated) || not (Env_level.equal nv.level pv.level)) (* avoid creating multiple UBs, if possible *) then begin
    fv_set_upper ~changes pv (UBvar nv :: pv.upper);
    subtype_lu ~changes env pv.lower (UBvar nv);
  end else begin
    assert (Env_level.extends pv.level nv.level);
    rotate_flex ~changes env pv;
    fv_set_lower ~changes nv (join_flexvars nv.lower (Fvset.single pv));
    nv.upper |> List.iter (fun n -> subtype_lu ~changes env (of_flexvar pv) n);
  end

and join_lower ~changes env level lower ty =
  (* FIXME: can join_lower ever raise?
      - If so, ensure SubtypeErrors are remapped correctly
      - If not, wrap in noerror *)
  match lower, ty with
  | Ltop (Some l), _ | _, Ltop (Some l) -> Ltop (Some l)
  | Ltop None, _ | _, Ltop None -> Ltop None
  | Lower (fva, ca), Lower (fvb, cb) ->
    (* (ca,fva) is already wf at level, (cb,fvb) may not be *)
    let resolve cons =
      let open Cons.One_or_two in
      Cons.map cons
        ~neg:(function
          | L l -> l
          | R r ->
             (* Not fresh_below_var, as hoisting may be needed.
                FIXME test this *)
             let v = fresh_flexvar level in
             noerror (fun () -> subtype_flex_flex ~changes env v r); v
          | LR (l, r) ->
             (* matchability *)
             noerror (fun () -> subtype_flex_flex ~changes env l r); l)
        ~pos:(function
          | L l -> l
          | R r ->
             (* Not necessarily id (matchability/levels) *)
             join_lower ~changes env level bottom r
          | LR (l, r) -> join_lower ~changes env level l r)
    in
    let join_cons conses c =
      resolve (Cons.join conses c)
    in
    let rvbounds, rvkeep =
      cb.rigvars |> Rvset.to_list_loc |> List.partition_map (fun ((rv : rigvar), loc) ->
        if Env_level.extends rv.level level then Right (rv,loc)
        else Left (env_rigid_bound env rv, loc)) (* FIXME loc *)
    in
    (* FIXME messy *)
    let exception Scope of Location.t option in
    match List.map (function None, l -> raise (Scope (match l with [] -> None | x::_ -> Some x)) | Some c, _ -> c) rvbounds with
    | exception Scope l -> Ltop l
    | rvbounds ->
    let cons = List.fold_left join_cons ca.cons (cb.cons :: rvbounds) in
    let rigvars = List.fold_left (fun acc (rv,l) -> Rvset.add acc rv l) ca.rigvars rvkeep in
    let fvb =
      (fvb :> flexvar list) |> List.filter_map (fun fv ->
        if Fvset.mem fv fva then None
        else if Env_level.extends fv.level level then Some fv
        else
          let fv' = fresh_flexvar level in
          noerror (fun () -> subtype_flex_flex ~changes env fv fv'); Some fv')
    in
    Lower (List.fold_left (Fvset.add ~merge:(fun a _ -> a)) fva fvb, { cons; rigvars })



let join_simple env a b =
  match a, b with
  | Lower(fva, {cons=consa; rigvars=rva}), Lower(fvb, {cons=consb; rigvars=rvb})
       when Cons.is_bottom consa || Cons.is_bottom consb ->
     (* easy case: only one side has cons, so no nontrivial joining to do *)
     Lower(Fvset.append fva fvb ~merge:(fun a _ -> a),
           {cons = if Cons.is_bottom consa then consb else consa;
            rigvars = Rvset.join rva rvb})
  | _ ->
     let changes = ref [] in
     let r = bottom in
     let r = join_lower ~changes env (env_level env) r a in
     let r = join_lower ~changes env (env_level env) r b in
     r

let check_simple t =
  let rec aux = function
    | Tsimple _ | Ttop _ | Tvar _ -> ()
    | Tjoin _ -> () (* by invariant *)
    | Tpoly _ -> raise Exit
    | Tcons c ->
       Cons.map ~neg:aux ~pos:aux c |> ignore
  in
  match aux t with
  | () -> true
  | exception Exit -> false

let upper_is_bot = function
  | UBcons {cons; rigvars} when Rvset.is_empty rigvars && Cons.is_bottom cons -> true
  | _ -> false

let rec instantiate_flex env vars body =
  let fvars = IArray.map (fun _ -> fresh_flexvar (env_level env)) vars in
  IArray.iter2 (fun (fv : flexvar) (_,t) ->
    let b =
      match t with
      | None -> None
      | Some t -> ntyp_to_upper ~simple:true env (open_typ_flex fvars t) in
    assert (fv.upper = [] && is_bottom fv.lower);
    match b with
    | None -> ()
    | Some b -> fv_set_upper ~changes:(ref []) fv [b])
    fvars vars;
  open_typ_flex fvars body

and ptyp_to_lower ~simple env : ptyp -> flex_lower_bound = function
  | Tsimple t -> t
  | Ttop l -> Ltop l
  | Tcons cons ->
     let cons = Cons.map ~neg:(ntyp_to_flexvar ~simple env) ~pos:(ptyp_to_lower ~simple env) cons in
     Lower(Fvset.empty, {cons; rigvars=Rvset.empty})
  | Tvar (_loc, Vbound _) -> intfail "Vbound"
  | Tvar (_loc, Vflex fv) -> of_flexvar fv
  | Tvar (loc, Vrigid rv) -> of_rigvar loc rv
  | Tjoin (a, b) -> join_simple env (ptyp_to_lower ~simple:true env a) (ptyp_to_lower ~simple:true env b)
  | Tpoly {vars; body} ->
     assert (not simple);
     let body = instantiate_flex env vars body in
     ptyp_to_lower ~simple env body

and ntyp_to_upper ~simple env : ntyp -> styp_neg option = function
  | Tsimple t -> Some (UBvar t)
  | Ttop _ -> None
  | Tcons cons ->
     let cons = Cons.map ~neg:(ptyp_to_lower ~simple env) ~pos:(ntyp_to_flexvar ~simple env) cons in
     Some (UBcons {cons; rigvars = Rvset.empty})
  | Tvar (_loc, Vbound _) -> intfail "Vbound"
  | Tvar (_loc, Vflex fv) -> Some (UBvar fv)
  | Tvar (loc, Vrigid rv) -> Some (UBcons {cons = Cons.bottom; rigvars = Rvset.singleton rv loc})
  | Tjoin (a, b) as ty ->
     begin match
       ntyp_to_upper ~simple:true env a, ntyp_to_upper ~simple:true env b
     with
     | Some (UBvar _), _ | _, Some (UBvar _) -> intfail "join of flexvar negatively: %a" pp_ntyp ty
     | None, _ | _, None -> None
     | Some (UBcons c1), Some (UBcons c2) ->
        (* only valid for nonoverlapping ctors *)
        let lr : _ Cons.One_or_two.t -> _ = function
          | L x | R x -> x
          | LR _ -> intfail "unexpected overlap"
        in
        let cons = Cons.join c1.cons c2.cons |> Cons.map ~neg:lr ~pos:lr in
        Some (UBcons { cons; rigvars = Rvset.join c1.rigvars c2.rigvars })
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
     let pos l _v =
       Tcons (match l with l :: _ -> Cons.bottom_loc l | _ -> Cons.bottom)
     in
     vars |> IArray.iteri (fun i (_, b) ->
       let b = Option.map (open_typ ~neg:pos ~pos:neg 0) b in
       let b = Option.map (ptyp_to_lower ~simple:true env) b in
       bounds.(i) <- b);
     let body = open_typ ~neg ~pos 0 body in
     ntyp_to_upper ~simple env body

and ntyp_to_flexvar ~simple env (t : ntyp) =
  match ntyp_to_upper ~simple env t with
  | None -> fresh_flexvar (env_level env)
  | Some (UBvar v) -> v
  | Some (UBcons c) ->
     let fv = fresh_flexvar (env_level env) in
     noerror (fun () -> subtype_lu ~changes:(ref []) env (of_flexvar fv) (UBcons c));
     fv

(*
 * Subtyping on typs (polymorphism)
 *)

let enter_rigid env vars rig_names =
  let level = Env_level.extend (env_level env) in
  let rvars = IArray.mapi (fun var _ -> {level; var}) vars in
  let temp_env =
    Env_types { level; rig_names;
                rig_defns = IArray.map (fun (name, _) ->
                    {name; upper=None}) vars; rest = env } in
  let rig_defns = IArray.map (fun (name, b) ->
     let upper =
       match b with
       | None -> Ltop (Some (snd name))
       | Some b -> ptyp_to_lower ~simple:true temp_env (open_typ_rigid rvars b) in
     match upper with
     | Ltop _ ->
        { name; upper = None}
     | Lower (fvs, ctor) ->
       (* FIXME: can you actually hit this?
          Try with a higher-rank type where the outer rank gets instantiated.
          Maybe change the type of the upper bound in parsed types.
          (to reflect its Tconsness)*)
        assert (Fvset.is_empty fvs);
        assert (Rvset.is_empty ctor.rigvars);
        { name; upper = Some ctor.cons }) vars in
  let env = Env_types { level; rig_names; rig_defns; rest = env} in
  env, rvars

(* FIXME: rank1 joins maybe?
   FIXME: keep types as Tcons if possible? Better inference. Can this matter? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  Tsimple (join_simple env (ptyp_to_lower ~simple:false env p) (ptyp_to_lower ~simple:false env q))

let rec subtype env (p : ptyp) (n : ntyp) =
  (* Format.printf "%a <= %a\n" pp_ptyp p pp_ntyp n; *)
  wf_ptyp env p; wf_ntyp env n;
  match p, n with
  | _, Ttop _ -> ()
  | Tcons cp, _ when Cons.is_bottom cp -> ()
  | Tcons cp, Tcons cn ->
     subtype_conses env ~neg:(subtype env) ~pos:(subtype env) cp {cons=cn;rigvars=Rvset.empty}
  | p, Tpoly {vars; body} ->
     let orig_env = env in
     let env, rvars = enter_rigid env vars SymMap.empty in
     let body = open_typ_rigid rvars body in
     (try subtype env p body
      with SubtypeError err ->
        raise (SubtypeError (close_err_rigid ~orig_env ~env vars err)))
  | Tpoly {vars; body}, n ->
     let body = instantiate_flex env vars body in
     subtype env body n; ()
  | p, ((Tsimple _ | Tvar _ | Tjoin _ | Tcons _) as n) ->
     match ntyp_to_upper ~simple:false env n with
     | None -> ()
     | Some u ->
        subtype_lu ~changes:(ref []) env (ptyp_to_lower ~simple:false env p) u; ()

let subtype env p n =
  (* FIXME: revert changes on failure? *)
  match subtype env p n with
  | exception SubtypeError e ->
     assert (fst e.env == env);
     Error e
  | () -> Ok ()

let rec match_typ env (p : ptyp) loc head =
  match p with
  | Tcons c ->
     subtype_conses env c {cons=head;rigvars=Rvset.empty}
       ~neg:(fun (_,v) t -> assert (!v = Ttop None); v := t)
       ~pos:(fun t (_,v) -> assert (!v = Tcons Cons.bottom); v := t);
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_typ env body loc head
  | t ->
     let instneg (_,v) =
       let fv = fresh_flexvar (env_level env) in
       v := Tsimple fv;
       ptyp_to_lower ~simple:true env (Tvar (Location.empty, Vflex fv)) in
     let shead = Cons.map ~neg:instneg ~pos:(fun _ -> ref bottom) head in
     match_sub ~changes:(ref []) env
       (ptyp_to_lower ~simple:false env t)
       {cons=shead; rigvars=Rvset.empty};
     noerror (fun () -> subtype_conses env shead {cons=head; rigvars=Rvset.empty}
       ~neg:(fun _ _ -> () (*already inserted by instneg*))
       ~pos:(fun t (_,v) -> v := Tsimple !t))

let match_typ env ty loc head =
  let head = Cons.map ~neg:(fun x -> x, ref (Ttop None)) ~pos:(fun x -> x, ref (Tcons Cons.bottom)) (Cons.make ~loc head) in
  wf_ptyp env ty;
  match match_typ env ty loc head with
  | exception SubtypeError e ->
     assert (fst e.env == env);
     Error e
  | () ->
     wf_ptyp env ty;
     Ok (Option.get (Cons.get_single (Cons.map ~neg:(fun (x, r) -> x, !r) ~pos:(fun (x, r) -> x, !r) head)))


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
  if Rvset.contains cn.rigvars rv then true
  else match subtype_lu ~changes env (lower_of_rigid_bound env (rv,[])) (UBcons cn) with
  | () when !changes = [] -> true
  | () ->
     (* Dubious case: we could also choose to keep these changes *)
     revert !changes; false
  | exception SubtypeError _ ->
     revert !changes; false

let spec_sub_rigid_pos env (rv : rigvar) p =
  let changes = ref [] in
  let bound =
    match env_rigid_bound env rv with
    | None -> Ltop None
    | Some cons -> Lower(Fvset.empty, {cons; rigvars=Rvset.empty})
  in
  match join_lower ~changes env (env_level env) p bound with
  | p' when equal_flex_lower_bound p p' && !changes = [] -> true
  | _ -> revert !changes; false


(* Returns true only if a <= b
   Not complete, never changes anything.
   Used only for optimisations, to avoid generalising a when x <= a <= x.
   Not a bug if it spuriously returns false sometimes (but leads to uglier types) *)
let rec clearly_subtype env (a :  flexvar) b : bool =
  match b with
  | Ltop _ -> true
  | Lower(flexvars, ctor) ->
  Fvset.mem a flexvars ||
  a.upper |> List.exists (function
  | UBvar a -> clearly_subtype env a b
  | UBcons cn ->
    Rvset.to_list cn.rigvars |> List.for_all (fun rv ->
      Rvset.contains ctor.rigvars rv) &&
    match
      (* FIXME: raise Exit? Is this actually used? *)
      subtype_conses env cn.cons ctor
        ~neg:(fun a b -> if not (clearly_subtype env a b) then raise Exit)
        ~pos:(fun a b -> if not (clearly_subtype env a b) then raise Exit)
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
    subtype_lu ~changes env lower (UBvar v);
    upper |> List.iter (function
      | UBvar v' -> subtype_flex_flex ~changes env v v'
      | UBcons c -> subtype_lu ~changes env (of_flexvar v) (UBcons c))
  end

let rec hoist_lower ~changes env level = function
  | Ltop _ -> ()
  | Lower(flexvars, ctor) ->
  (* FIXME hoisting: this looks wrong: what about the levels of ctor.rigvars?  *)
  map_ctor_rig (hoist_flex ~changes env level) (hoist_lower ~changes env level) ctor |> ignore;
  Fvset.iter flexvars ~f:(hoist_flex ~changes env level);
  ()

let rec expand visit ~changes ?vexpand env = function
  | Ltop _ as p -> p
  | Lower(flexvars, ctor) as p ->
     wf_flex_lower_bound ~seen:(Hashtbl.create 10) env (env_level env) p;
     expand' visit ~changes ?vexpand env flexvars ctor
and expand' visit ~changes ?(vexpand=[]) env pflexvars pctor =
  let level = env_level env in
  let flexvars_gen, flexvars_keep = Fvset.partition ~f:(fun fv -> Env_level.equal fv.level level) pflexvars in
  Fvset.iter flexvars_gen ~f:(fun pv ->
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
         let lower =
           match lower with
           | Ltop _ as p -> p
           | Lower (flexvars, c) -> Lower (Fvset.filter ~f:(fun v -> not (equal_flexvar v pv)) flexvars, c) in
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
      level (flexvars_keep :> flexvar list) in


  let p = Lower(Fvset.empty, pctor) in
  let p =
    (* FIXME: noerror? *)
    if Env_level.equal level keep_level then p
    else noerror (fun () -> 
          hoist_lower ~changes env keep_level p;
          join_lower ~changes env keep_level bottom p) in

  match p with
  | Ltop _ as p -> p
  | Lower(_pflexvars, pctor) ->
     (* FIXME _pflexvars?? *)

  let cons = Cons.map ~neg:(expand_fv_neg visit ~changes env) ~pos:(expand visit ~changes env) pctor.cons in
  let rigvars = pctor.rigvars |> Rvset.filter (fun rv ->
    not (spec_sub_rigid_pos env rv (Lower(Fvset.empty,{cons;rigvars=Rvset.empty})))) in
  let ctor = { cons; rigvars } in

  (* NB: flexvars_gen occurs twice below, re-adding the reflexive constraints: α expands to (α|α.lower) *)
  (* NB: this is careful to preserve order if no change is made *)
  let joined =
    List.fold_left (fun p v -> join_lower ~changes env level p v.lower)
      (Lower(flexvars_keep, ctor))
      (flexvars_gen :> flexvar list) in
  match joined with
  | Ltop _ as p -> p
  | Lower(flexvars_exp, ctor) ->

  let flexvars_exp_gen, flexvars_keep = Fvset.partition ~f:(fun fv -> Env_level.equal fv.level level) flexvars_exp in
  (* C|a = C, if a <= C, so we might be able to drop some flexvars *)
  let flexvars_gen =
    Fvset.append flexvars_gen flexvars_exp_gen ~merge:(fun a _ -> a)
    |> Fvset.filter ~f:(fun fv -> not (clearly_subtype env fv (Lower(flexvars_keep, ctor)))) in
  Lower(Fvset.append flexvars_keep flexvars_gen ~merge:(fun a _ -> a), ctor)


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
       let all_rigvars = List.fold_left (fun s c -> Rvset.join s c.rigvars) Rvset.empty cns in
       let keep_rigvars = all_rigvars |> Rvset.filter (fun rv ->
         cns |> List.for_all (fun cn -> spec_sub_rigid_cons env rv cn)) in
       (* FIXME: used to be cons=Top; rigvars, which makes no sense? *)
       (* FIXME is this hitting more often?
 *)
       fv_maybe_set_upper ~changes nv [UBcons {cons=Cons.bottom; rigvars = keep_rigvars}] |> ignore;
       (* FIXME noerror? *)
       noerror (fun () ->
         cns |> List.iter (fun cn ->
           subtype_lu ~changes env (of_flexvar nv) (UBcons {cn with rigvars = keep_rigvars }));
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
  | Ttop _ as t -> t
  | Tcons c ->
     Tcons (Cons.map
              ~neg:(map_typ_simple ~pos:neg ~neg:pos ~index)
              ~pos:(map_typ_simple ~neg ~pos ~index)
              c)
  | Tjoin (a, b) -> Tjoin(map_typ_simple ~neg ~pos ~index a, map_typ_simple ~neg ~pos ~index b)
  | Tvar (l, Vbound v) -> Tvar (l, Vbound v)
  | Tsimple _
  | Tvar (_, (Vflex _ | Vrigid _)) as t ->
     pos ~index t
  | Tpoly {vars; body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (n, t) -> n, Option.map (map_typ_simple ~neg:pos ~pos:neg ~index) t) vars in
     let body = map_typ_simple ~neg ~pos ~index body in
     Tpoly {vars; body}

let expand_typ visit ~changes env =
  let pos ~index:_ t =
    let t = ptyp_to_lower ~simple:true env t in
    let t' = expand visit ~changes env t in
    if not (equal_flex_lower_bound t t') then
      changes := Change_expanded_mark :: !changes;
    Tsimple t' in
  let neg ~index:_ t =
    Tsimple (expand_fv_neg visit ~changes env (ntyp_to_flexvar ~simple:true env t)) in
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
  fun s lb ->
  match lb with
  | Ltop loc -> Ttop loc
  | Lower (flexvars, {cons;rigvars}) ->
  let cons = Cons.map ~neg:(substn_fv_neg s) ~pos:(substn s) cons in
  let rigvars_gen, rigvars_keep = Rvset.peel_level s.level rigvars in
  let flexvars_gen, flexvars_keep = Fvset.partition ~f:(fun (fv:flexvar) -> Env_level.equal fv.level s.level) flexvars in
  Fvset.iter flexvars_gen ~f:(fun fv -> assert (is_visited_pos s.visit fv));

  let rigvars_gen = rigvars_gen |> List.map (fun ((rv:rigvar), l) ->
    l, Vbound {index = s.index; var = rv.var}) in
  let rigvars_keep = Rvset.to_list_loc rigvars_keep |> List.map (fun (rv,l) -> l, Vrigid rv) in
  let flexvars_gen = (flexvars_gen :> flexvar list) |> List.filter_map (substn_bvar s) |> List.concat in
  let flexvars_keep = (flexvars_keep :> flexvar list) |> List.map (fun fv -> Location.empty, Vflex fv) in

  (* FIXME pick a better comparison function *)
  let flexvars_gen = List.sort compare flexvars_gen in
  let tvars = (rigvars_keep @ flexvars_keep @ rigvars_gen @ flexvars_gen) in

  let cons = tcons cons in
  tvjoin ~base:cons tvars
    

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
  | [] -> Ttop None
  | _ :: _ :: _ -> intfail "multirig gen"
  | [UBvar v] -> substn_fv_neg s v
  | [UBcons {cons;rigvars}] ->
     let cons = Cons.map ~neg:(substn s) ~pos:(substn_fv_neg s) cons in
     let rigvars_gen, rigvars_keep = Rvset.peel_level s.level rigvars in
     let rigvars_gen = rigvars_gen |> List.map (fun (v,l) ->
       assert (Vector.get s.bvars v.var = Gen_rigid v);
       l, Vbound {index=s.index; var=v.var}) in
     let rigvars_keep =
       Rvset.to_list_loc rigvars_keep |> List.map (fun (v,l) -> l, Vrigid v) in
     (* FIXME is this still needed? *)
     match Cons.is_bottom cons, rigvars_keep, rigvars_gen, s.mode with
     | true, [], [l,v], _ -> Tvar (l,v)
     | _, [], [], _ -> tcons cons
     | _, rigvars, _, `Poly ->
        (* Drop rigvars_gen to avoid making contravariant joins *)
        (* FIXME dubious *)
        List.fold_left (fun c (l,r) -> tjoin c (Tvar (l, r))) (tcons cons) rigvars
     | _, rv_keep, rv_gen, `Elab ->
        (* FIXME: this is wrong, I think. Be careful about Tvjoin invariants *)
        List.fold_left (fun c (l,r) -> tjoin c (Tvar (l, r))) (tcons cons) (rv_keep @ rv_gen)


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
           let n = Vector.push s.bvars (Gen_flex (fv, Ttop None)) in
           Generalised n
         | [UBcons {cons;rigvars}] ->
            if
              rigvars |> Rvset.to_list |> List.for_all (fun rv ->
                spec_sub_rigid_cons s.env rv {cons;rigvars=Rvset.empty})
            then
              let bound = substn_upper {s with index=0}
                            [UBcons {cons;rigvars=Rvset.empty}] in
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
