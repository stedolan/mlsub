open Util
open Typedefs

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)

type err_typ = (unit, unit) typ
type subtyping_error = {
  lhs : err_typ;
  rhs : err_typ;
  err : Cons.conflict;
  located : (err_typ Location.loc * err_typ Location.loc) option;
  env : env * string iarray list;
}
let err_typ_cons conses =
  let c = Cons.{ conses; locs = Cons.Locs.empty } in
  (* FIXME: keep some parts? *)
  Tcons (Cons.map ~pos:(fun _ -> Tsimple ()) ~neg:(fun _ -> Tsimple ()) c)

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
    located |> Option.map (fun ((a,al),(b,bl)) ->
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
  tvjoin ~base:(cons_head cons) (List.map (fun (rv,l) -> Some l,Vrigid rv) (Rvset.to_list rigvars))

let ctor_pick_loc {cons;rigvars} =
  match Cons.Locs.pick cons.locs, Rvset.to_list rigvars with
  | Some (_, l), _ -> Some l
  | None, (_, l) :: _ -> Some l
  | _ -> None

let subtype_conses env ~neg ~pos cp cn =
  match Cons.subtype cp cn.cons with
  | Error {conflict=err; located} ->
     let located =
       match located, Rvset.to_list cn.rigvars with
       | None, (rv, rl) :: _ ->
          Some ((err_typ_cons cp.conses, Option.get (ctor_pick_loc {cons=cp;rigvars=Rvset.empty})), (Tvar (Some rl, Vrigid rv), rl))
       | Some ((cp,lp),(cn,ln)), _ ->
          Some ((err_typ_cons cp,lp),(err_typ_cons cn,ln))
       | None, [] ->
          None
     in
     raise (SubtypeError {lhs=cons_head cp; rhs=ctor_head cn; err; located; env=(env,[])})
  | Ok subs ->
     let sub fn field a b =
       try fn a b
       with SubtypeError {lhs; rhs; err; located; env} ->
         let wrap outer inner =
           let neg k _x = if Cons.equal_field (F_neg k) field then inner else Tsimple () in
           let pos k _x = if Cons.equal_field (F_pos k) field then inner else Tsimple () in
           Tcons (Cons.mapi ~neg ~pos outer)
         in
         let err =
           match field with
           | F_pos _ -> {lhs = wrap cp lhs; rhs = wrap cn.cons rhs; err; located; env}
           | F_neg _ -> {lhs = wrap cp rhs; rhs = wrap cn.cons lhs; err; located; env}
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
  | None -> Ltop (Some rvloc)
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
          Some ((Ttop (Some l), l), (ctor_head cn, r))
       | _ -> None
     in
     raise (SubtypeError {lhs=Ttop loc; rhs=ctor_head cn; err=Incompatible; located; env=(env,[])})
  | Lower(pflex, {cons; rigvars}) ->
     (* constructed type *)
     subtype_conses env cons cn
       ~neg:(fun p n -> subtype_lu ~changes env p (UBvar n))
       ~pos:(fun p r -> r := join_lower ~changes env (env_level env) !r p);
     (* rigid variables *)
     Rvset.to_list rigvars
     |> List.filter (fun rvl -> not (Rvset.mem rvl cn.rigvars))
     |> List.iter (fun (rv, rvloc) ->
       try match_sub ~changes env (lower_of_rigid_bound env (rv, rvloc)) cn
       with SubtypeError err ->
         let lhs = Tvar (Some rvloc, Vrigid rv) in
         let located =
           (* In the case where the rv has a nontrivial bound,
              maybe we should report that location instead? Or as well? *)
           err.located |> Option.map (fun ((_l,_lloc),(r,rloc)) ->
              ((lhs,rvloc),(r,rloc)))
         in
         raise (SubtypeError {err with lhs; located}));
     (* flexible variables *)
     Fvset.iter pflex ~f:(fun pv ->
       let cn =
         match List.partition (fun ((rv:rigvar),_) -> Env_level.extends rv.level pv.level) (Rvset.to_list cn.rigvars) with
         | _, [] -> cn
         | _rigvars, drop ->
            let drop =
              drop |> List.map (fun (_, l) -> ([], l)) in
            { cons = { cn.cons with locs = Cons.Locs.append' cn.cons.locs drop ~merge:(fun a _ -> a) };
              rigvars = (*FIXME*) Rvset.filter ~f:(fun (rv,_) -> Env_level.extends rv.level pv.level) cn.rigvars }
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
     if fv_maybe_set_lower ~changes nv lower then begin
       ensure_rigvars_present ~changes env nv;
       nv.upper |> List.iter (fun n -> subtype_lu ~changes env p n);
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
          Rvset.to_list rvlow |> List.for_all (fun rv -> Rvset.mem rv rigvars)) in
     match recheck with
     | [] -> ()
     | recheck ->
        fv_set_upper ~changes fv keep;
        recheck |> List.iter (function
          | UBvar _ -> assert false
          | UBcons cb ->
            let cb = { cb with rigvars = Rvset.append cb.rigvars rvlow ~merge:(fun a _ -> a) } in
            (* This shouldn't fail because we already have fv <= cb *)
            noerror (fun () -> subtype_lu ~changes env (of_flexvar fv) (UBcons cb)))

and rotate_flex ~changes env (pv : flexvar) =
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
  | Lower (fva, {cons=consa; rigvars=rva}), Lower (fvb, {cons=consb; rigvars=rvb}) ->
    (* (ca,fva) is already wf at level, (cb,fvb) may not be *)
    let resolve cons =
      let open Cons.One_or_two in
      Cons.map cons
        ~neg:(function
          | L l -> l
          | R r ->
             let fv' = fresh_flexvar level in
             noerror (fun () -> subtype_flex_flex ~changes env fv' r); fv'
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
    let fvb =
      (fvb :> flexvar list) |> List.map (fun fv ->
         if Env_level.extends fv.level level then fv
         else let fv' = fresh_flexvar level in
              noerror (fun () -> subtype_flex_flex ~changes env fv fv'); fv')
    in
    let fv = List.fold_left (Fvset.add ~merge:(fun a _ -> a)) fva fvb in
    let rec join_rigvars cons rigvars = function
      | [] -> Lower(fv, {cons; rigvars})
      | ((rv:rigvar), loc) :: rest when Env_level.extends rv.level level ->
         join_rigvars cons (Rvset.add rigvars (rv, loc) ~merge:(fun a _ -> a)) rest
      | (rv, loc) :: rest ->
         match env_rigid_bound env rv with
         | None -> Ltop (Some loc)
         | Some bound -> join_rigvars (resolve (Cons.join cons bound)) rigvars rest
    in
    join_rigvars (resolve (Cons.join consa consb)) rva (Rvset.to_list rvb)


let join_simple env a b =
  match a, b with
  | Lower(fva, {cons=consa; rigvars=rva}), Lower(fvb, {cons=consb; rigvars=rvb})
       when Cons.is_bottom consa || Cons.is_bottom consb ->
     (* easy case: only one side has cons, so no nontrivial joining to do *)
     Lower(Fvset.append fva fvb ~merge:(fun a _ -> a),
           {cons = if Cons.is_bottom consa then consb else consa;
            rigvars = Rvset.append rva rvb ~merge:(fun a _ -> a)})
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
  let fvneg _loc i = Tsimple (IArray.get fvars i) in
  let fvpos _loc i = Tsimple (of_flexvar (IArray.get fvars i)) in
  IArray.iter2 (fun (fv : flexvar) (_,t) ->
    let b =
      match t with
      | None -> None
      | Some t -> ntyp_to_upper ~simple:true env (open_typ ~neg:fvpos ~pos:fvneg 0 t) in
    assert (fv.upper = [] && is_bottom fv.lower);
    match b with
    | None -> ()
    | Some b -> fv_set_upper ~changes:(ref []) fv [b])
    fvars vars;
  open_typ ~neg:fvneg ~pos:fvpos 0 body

and ptyp_to_lower ~simple env : ptyp -> flex_lower_bound = function
  | Tsimple t -> t
  | Ttop l -> Ltop l
  | Tcons cons ->
     let cons = Cons.map ~neg:(ntyp_to_flexvar ~simple env) ~pos:(ptyp_to_lower ~simple env) cons in
     Lower(Fvset.empty, {cons; rigvars=Rvset.empty})
  | Tvar (_loc, Vbound _) -> intfail "Vbound"
  | Tvar (loc, Vrigid rv) -> of_rigvar (match loc with None -> Location.noloc | Some l -> l) rv
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
  | Tvar (loc, Vrigid rv) ->
     let loc = match loc with None -> Location.noloc | Some l -> l in
     Some (UBcons {cons = Cons.bottom; rigvars = Rvset.single (rv, loc)})
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
        Some (UBcons { cons; rigvars = Rvset.append c1.rigvars c2.rigvars ~merge:(fun a _ -> a) })
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
       Tcons (match l with None -> Cons.bottom | Some l -> Cons.bottom_loc l)
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
       of_flexvar fv in
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
let spec_sub_rigid_cons env ((rv : rigvar), loc) cn =
  let changes = ref [] in
  if Rvset.mem (rv,loc) cn.rigvars then true
  else match subtype_lu ~changes env (lower_of_rigid_bound env (rv,Location.noloc)) (UBcons cn) with
  | () when !changes = [] -> true
  | () ->
     (* Dubious case: we could also choose to keep these changes *)
     revert !changes; false
  | exception SubtypeError _ ->
     revert !changes; false

let spec_sub_rigid_pos env ((rv : rigvar), _loc) p =
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
      Rvset.mem rv ctor.rigvars) &&
    match
      (* FIXME: raise Exit? Is this actually used? *)
      subtype_conses env cn.cons ctor
        ~neg:(fun a b -> if not (clearly_subtype env a b) then raise Exit)
        ~pos:(fun a b -> if not (clearly_subtype env a b) then raise Exit)
    with
    | exception SubtypeError _ -> false
    | () -> true)


(* This function could be optimised by skipping subtrees that have no use
   of the outermost level, Remy-style *)
let rec map_typ_simple : 'neg1 'pos1 'neg2 'pos2 .
  neg:(index:int -> ('pos1,'neg1) typ -> ('pos2, 'neg2) typ) ->
  pos:(index:int -> ('neg1,'pos1) typ -> ('neg2, 'pos2) typ) ->
  index:int -> ('neg1, 'pos1) typ -> ('neg2, 'pos2) typ =
  fun ~neg ~pos ~index -> function
  | Ttop _ as t -> t
  | Tcons c ->
     Tcons (Cons.map
              ~neg:(map_typ_simple ~pos:neg ~neg:pos ~index)
              ~pos:(map_typ_simple ~neg ~pos ~index)
              c)
  | Tjoin (a, b) -> Tjoin(map_typ_simple ~neg ~pos ~index a, map_typ_simple ~neg ~pos ~index b)
  | Tvar (l, (Vbound _ as v)) -> Tvar (l, v)
  | Tsimple _
  | Tvar (_, Vrigid _) as t ->
     pos ~index t
  | Tpoly {vars; body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (n, t) -> n, Option.map (map_typ_simple ~neg:pos ~pos:neg ~index) t) vars in
     let body = map_typ_simple ~neg ~pos ~index body in
     Tpoly {vars; body}

(* FIXME: bit weird... There must be a better representation for bvars here *)

type genvar =
  (* FIXME drop flexvar here *)
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

let remove_flexvar fv = function
  | Lower(fvs, c) when Fvset.mem fv fvs ->
     Lower(Fvset.filter ~f:(fun v -> not (equal_flexvar v fv)) fvs, c)
  | p -> p

let optimise_lower env = function
  | Ltop _ as p -> p
  | Lower(flexvars, {cons; rigvars}) ->
     (* MLsub-style entailment optimisation: in (α ∧ {foo: β}) → (α ∨ {foo: β}), α is redundant *)
     let flexvars = Fvset.filter flexvars ~f:(fun fv ->
       not (clearly_subtype env fv (Lower(Fvset.empty, {cons;rigvars})))) in
     (* FIXME: unify spec_sub_rigid_pos and clearly_subtype *)
     let rigvars = rigvars |> Rvset.filter ~f:(fun rv ->
       not (spec_sub_rigid_pos env rv (Lower(Fvset.empty,{cons;rigvars=Rvset.empty})))) in
     Lower(flexvars, {cons; rigvars})

let rec expand_lower visit ~changes ?(vexpand=[]) env = function
  | Ltop _ as p -> p
  | Lower(flexvars, {cons; rigvars}) ->
     let level = env_level env in
     let fv_here, _fv_there =
       Fvset.partition flexvars
         ~f:(fun fv -> Env_level.equal fv.level level)
     in
     Fvset.iter fv_here ~f:(fun pv ->
       fv_gen_visit_pos env visit pv (function
         | Recursive_visit ->
            (* recursive occurrences are fine if not under a constructor *)
            if not (List.memq pv vexpand)
            then unimp "positive recursion on flexvars"
         | First_visit ->
            rotate_flex ~changes env pv;
            (* Add pv to expand so we ignore it if seen before the next ctor *)
            let lower = expand_lower visit ~changes ~vexpand:(pv::vexpand) env pv.lower in
            if fv_maybe_set_lower ~changes pv (remove_flexvar pv lower) then
              ensure_rigvars_present ~changes env pv));
     let cons = Cons.map ~neg:(expand_fv_neg visit ~changes env) ~pos:(expand_lower visit ~changes env) cons in
     List.fold_left
       (fun acc fv -> join_lower ~changes env level acc fv.lower)
       (Lower(flexvars, {cons; rigvars}))
       (fv_here :> flexvar list)
     |> optimise_lower env

and expand_fv_neg visit ~changes env nv =
  fv_gen_visit_neg env visit nv (function
    | Recursive_visit ->
       unimp "neg cycle on recursive flexvar"
    | First_visit ->
       match nv.upper with
       | [] -> ()
       | [UBvar v] when Env_level.equal nv.level v.level ->
          ignore (expand_fv_neg visit ~changes env v)
       | _ ->
          rotate_flex ~changes env nv;
          let conses, vars =
            nv.upper |> List.partition_map (function
              | UBvar v as u ->
                 assert (not (Env_level.equal v.level nv.level));
                 Right u
              | UBcons c -> Left c)
          in
          match conses with
          | [] -> ()
          | [{cons; rigvars}] ->
             let cons = Cons.map ~neg:(expand_lower visit ~changes env) ~pos:(expand_fv_neg visit ~changes env) cons in
             (* FIXME: any point to this?
             let rigvars = rigvars |> Rvset.filter ~f:(fun rv ->
               not (spec_sub_rigid_cons env rv {cons; rigvars=Rvset.empty})) in*)
             ignore (fv_maybe_set_upper ~changes nv (UBcons {cons; rigvars} :: vars))
          | _cons ->
             (* FIXME: better error reporting (list rv candidates, at least) *)
             (* FIXME: could drop some with spec_sub? *)
             (* FIXME: maybe this should move to promote, so that occurrences in Elab don't break things? *)
             unimp "multi RV upper bounds"
  );
  nv


let expand_typ visit ~changes env =
  let pos ~index:_ t =
    let t = ptyp_to_lower ~simple:true env t in
    let t' = expand_lower visit ~changes env t in
    if not (equal_flex_lower_bound t t') then
      changes := Change_expanded_mark :: !changes;
    Tsimple t' in
  let neg ~index:_ t =
    Tsimple (expand_fv_neg visit ~changes env (ntyp_to_flexvar ~simple:true env t)) in
  map_typ_simple ~neg:pos ~pos:neg ~index:0, map_typ_simple ~neg ~pos ~index:0

let expand_ntyp visit ~changes env = fst (expand_typ visit ~changes env)
let expand_ptyp visit ~changes env = snd (expand_typ visit ~changes env)

(* FIXME: does not yet detect the creation of contravariant joins
   during promotion. These arise (only?) during promotions with
   rigvars at the current level. *)


type ('n, 'p) promotion_policy =
  | Policy_hoist : env -> (flexvar, flex_lower_bound) promotion_policy
  | Policy_generalise : (zero, zero) promotion_policy

type ('n, 'p) promote_info = {
  visit: int;
  bvars: genvar Vector.t;
  env: env;
  level: Env_level.t;
  index: int;
  mode: [`Poly | `Elab];
  policy : ('n, 'p) promotion_policy;
}


(* After expansion, negatively reachable variables will have upper
   bounds in a particular form *)
type expanded_upper =
  (* EUB_var v - v at same level *)
  | EUB_var of flexvar
  (* EUB_cons (c, vs) - none of vs at same level *)
  | EUB_cons of (flex_lower_bound, flexvar) ctor_ty option * flexvar list
let get_upper (s : (_, _) promote_info) (fv : flexvar) =
  assert (is_visited_neg s.visit fv);
  match fv.upper with
  | [UBvar v] when Env_level.equal v.level s.level ->
     assert (not (is_visited_pos s.visit fv));
     EUB_var v
  | us ->
     let ctors, vars =
       us |> List.partition_map (function
         | UBvar v -> assert (not (Env_level.equal v.level s.level)); Right v
         | UBcons ctor -> Left ctor)
     in
(*
     begin match vars with
     | [] -> ()
     | _ :: _ ->
        assert (s.policy <> Policy_generalise); (* MonoLocalBinds *)
     end;
*)
     match ctors with
     | [] -> EUB_cons (None, vars)
     | [c] -> EUB_cons (Some c, vars)
     | _ :: _ :: _ -> intfail "multiple UBcons even after expansion"

let promote_rigvars s rvs =
  rvs |> Rvset.to_list |> List.map (fun ((rv:rigvar), loc) ->
    if Env_level.equal rv.level s.level
    then (assert (Vector.get s.bvars rv.var = Gen_rigid rv);
          Some loc, Vbound {index=s.index; var=rv.var})
    else Some loc, Vrigid rv)

type ('n, 'p) promote_flexvar_result =
  | Generalised : int -> (zero, zero) promote_flexvar_result
  | Hoisted : flexvar -> (flexvar, flex_lower_bound) promote_flexvar_result

let rec promote_lower :
  type n p . (n, p) promote_info -> flex_lower_bound -> (n, p) typ =
  fun s lb -> match lb with
  | Ltop loc -> Ttop loc
  | Lower (flexvars, {cons; rigvars}) -> 
     (* FIXME: variable sort order below *)
     let cons = Cons.map ~neg:(promote_fv_neg s) ~pos:(promote_lower s) cons in
     let rigvars = promote_rigvars s rigvars in
     let t = tvjoin ~base:(tcons cons) (List.sort compare rigvars) in
     match List.filter_map (promote_flexvar s) (flexvars :> flexvar list) with
     | [] -> t
     | flexvars ->
        match s.policy with
        | Policy_generalise ->
           let flexvars = List.map (fun (Generalised var) -> None, Vbound {index=s.index; var}) flexvars in
           (* FIXME use a better sort *)
           tvjoin ~base:t (List.sort compare flexvars)
        | Policy_hoist _env ->
           let flexvars = List.map (fun (Hoisted fv) -> fv) flexvars in
           (* FIXME: This can create joins between Tcons containing Vbound and flexvars.
              Is this OK? They can only come up in explicit polymorphism w/ unannotated deps *)
           tjoin t (Tsimple (of_flexvars (Fvset.of_list ~merge:(fun a _ -> a) flexvars)))

and promote_fv_neg :
  type n p . (n, p) promote_info -> flexvar -> (p, n) typ =
  fun s nv ->
  match promote_flexvar s nv, s.policy with
  | None, _ -> 
     (* substitute away the variable *)
     begin match get_upper s nv with
     | EUB_var nv' -> promote_fv_neg s nv'
     | EUB_cons (None, []) -> Ttop None
     | EUB_cons (Some {cons; rigvars}, []) ->
       let cons = Cons.map ~neg:(promote_lower s) ~pos:(promote_fv_neg s) cons in
       (* FIXME: can this create contravariant joins?
          (Previous version dropped rigvars_gen here, which is dubious) *)
       let rigvars = promote_rigvars s rigvars in
       tvjoin ~base:(tcons cons) rigvars
     | EUB_cons (_, _ :: _) ->
        (* should have been promote_flexvar'd *)
        assert false
     end
  | Some (Generalised var), Policy_generalise ->
     let v = Vbound {index=s.index; var} in
     assert (is_visited_pos s.visit nv);
     begin match s.mode with
     | `Poly -> Tvar (None, v)
     | `Elab ->
        (* Here a positive type is used as negative, but only when:
           - Elab, so placement of rigid variables doesn't matter
           - Policy_generalise, so there are no flexible variables *)
        tvjoin ~base:(promote_lower s nv.lower) [(None, v)]
     end
  | Some (Hoisted v), Policy_hoist hoist_env ->
     assert (Env_level.extends v.level (env_level hoist_env));
     Tsimple v

and promote_flexvar :
  type n p . (n, p) promote_info -> flexvar -> (n, p) promote_flexvar_result option =
  fun s fv ->
  if not (Env_level.equal fv.level s.level) then
    match s.policy with
    | Policy_hoist hoist_env ->
       assert (Env_level.extends fv.level (env_level hoist_env));
       Some (Hoisted fv)
    | Policy_generalise ->
       intfail "Flexible variable found during generalisation" (* MonoLocalBinds *)
  else begin
  assert (Env_level.equal fv.level s.level);
  match fv.gen with
  | Not_generalising -> assert false
  | Generalising gen ->
     let upper_requires_hoist = function
       | [UBvar v] when Env_level.equal v.level s.level -> false
       | [] | [UBcons _] -> false
       | _ -> true
     in
     if not (gen.visit.neg = s.visit && (gen.visit.pos = s.visit || upper_requires_hoist fv.upper))
     then None
     else match gen.bound_var with
     | Computing_bound ->
        (* FIXME: detect all recursion cases during expand so this can go away *)
        unimp "flexvar recursive in own bound"
     | Generalised var ->
        (match s.policy with Policy_generalise -> Some (Generalised var) | _ -> assert false)
     | Kept fv ->
        (match s.policy with Policy_hoist _ -> Some (Hoisted fv) | _ -> assert false)
     | Replace_with_rigid _ ->
        assert false
     | No_var_chosen ->
        gen.bound_var <- Computing_bound;
        let bv : flexvar_gen_status =
          assert (is_visited_pos s.visit fv || upper_requires_hoist fv.upper);
          let vars, upper =
            match get_upper s fv with
            | EUB_cons (None, vars) -> vars, Ttop None
            | EUB_cons (Some {cons;rigvars}, vars) ->
               let cons = Cons.map ~neg:(promote_lower s) ~pos:(promote_fv_neg s) cons in
               (* FIXME: can this create contravariant joins? *)
               (* FIXME: consider dropping some with spec_sub_rigid_cons *)
               let rigvars = promote_rigvars s rigvars in
               vars, tvjoin ~base:(tcons cons) rigvars
            | EUB_var _ -> assert false
          in
          match s.policy with
          | Policy_generalise ->
            assert (vars = []); (* since visited_pos *)
            let n = Vector.push s.bvars (Gen_flex (fv, gen_zero upper)) in
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


let substn_typ (type p) (type n) (s : (n, p) promote_info) =
  let simple = function
    | Tsimple t -> t
    | _ -> intfail "subst on unexpanded simple type" in
  let pos ~index t : ptyp =
    let t = promote_lower {s with index} (simple t) in
    match s.policy with Policy_generalise -> gen_zero t | Policy_hoist _ -> t
  in
  let neg ~index t : ntyp =
    let t = promote_fv_neg {s with index} (simple t) in
    match s.policy with Policy_generalise -> gen_zero t | Policy_hoist _ -> t
  in
  map_typ_simple ~neg:pos ~pos:neg ~index:s.index, map_typ_simple ~neg ~pos ~index:s.index

let substn_ntyp ~mode ~policy ~visit ~bvars ~env ~index (t : ntyp) : ntyp =
  match policy with
  | `Generalise ->
     let s = { mode; policy = Policy_generalise; visit; bvars; env; level = env_level env; index } in
     fst (substn_typ s) t
  | `Hoist henv ->
     let s = { mode; policy = Policy_hoist henv; visit; bvars; env; level = env_level env; index } in
     fst (substn_typ s) t

let substn_ptyp ~mode ~policy ~visit ~bvars ~env ~index (t : ptyp) : ptyp =
  match policy with
  | `Generalise ->
     let s = { mode; policy = Policy_generalise; visit; bvars; env; level = env_level env; index } in
     snd (substn_typ s) t
  | `Hoist henv ->
     let s = { mode; policy = Policy_hoist henv; visit; bvars; env; level = env_level env; index } in
     snd (substn_typ s) t
