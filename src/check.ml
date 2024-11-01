open Util
open Tuple_fields
open Exp
open Typedefs
open Types
open Error

let unit loc = tcons (Record {tag=Some Anon_tag; args=[]; body={fnames=[]; fields=FieldMap.empty}}, loc)

open Elab

type generalisation_mode = {
  mutable gen_level_acc: env_level option;
}

let fresh_gen_mode () : generalisation_mode =
  { gen_level_acc = None }

let mark_var_use_at_level ~(mode : generalisation_mode) lvl =
  mode.gen_level_acc <-
    match mode.gen_level_acc, lvl with
    | None, x | x, None -> x
    | Some l1, Some l2 ->
       Some (Env_level.min l1 l2)

module Promotion = Types.Promotion (struct
  type t = ptyp * Elab.typed_action
  let map ~neg ~pos (ty, act) =
    let ty = pos ~mode:`Poly ~ext:[] ty in
    let act = typed_map_typs_action act ~ext:[]
                ~neg:(neg ~mode:`Elab)
                ~pos:(pos ~mode:`Elab)
    in
    (ty, act)
end)

(* FIXME:
   This improves elaborations but is a bit of a hack.
   Decide whether to keep it! *)
let elab_ptyp = function
  | Tsimple [Lflexvar v] -> Elab_ntyp (Tsimple v)
  | ty -> Elab_ptyp ty

let fresh_flow env : ntyp * ptyp =
  let fv = fresh_flexvar (Env.level env) in
  Tsimple fv, Tsimple [Lflexvar fv]

type vtyp = (flexvar, flexvar) typ
let ptyp_of_vtyp (t : vtyp) : ptyp =
  Types.map_typ_1 ~neg:(fun x -> x) ~pos:(fun x -> [Lflexvar x]) ~index:0 t
let ntyp_of_vtyp (t : vtyp) : ntyp =
  Types.map_typ_1 ~pos:(fun x -> x) ~neg:(fun x -> [Lflexvar x]) ~index:0 t

module Mode = struct
  type t =
    | Checking of ntyp
    | Inference of ptyp ref
    | Transparent of
        (* "Simultaneous Input and Output", e.g. sec 6.4 of Bidirectional Typing *)
        { checking: vtyp;
          mutable inference: ptyp option }

  let checking ty =
    Checking ty

  let inferring () =
    Inference (ref (tbot (Some (Location.fixme "inference"))))

  let transparent ty =
    Transparent
      { checking = ty;
        inference = None }

  let dup = function
    | Checking _ | Inference _ as t -> t
    | Transparent r -> Checking (ntyp_of_vtyp r.checking)

  let wf env = function
    | Checking t -> wf_ntyp env t
    | Inference _ -> ()
    | Transparent {checking=t;inference=_} -> wf_ntyp env (ntyp_of_vtyp t)

  let inferred_type env ty =
    let t = match ty with
      | Checking _ -> intfail "Mode.result in Checking mode"
      | Inference r -> !r
      | Transparent {checking; inference=None} -> ptyp_of_vtyp checking
      | Transparent {checking=_; inference=Some p} -> p
    in
    wf_ptyp env t;
    t

  let transparent_inferred_type env ty =
    match ty with
    | Checking _ | Inference _ -> intfail "Mode.transparent_inferred_type: wrong mode"
    | Transparent {checking = _; inference = None} -> None
    | Transparent {checking = ck; inference = Some inf} ->
       (* We know inf <= ck. So if ck <= inf, they're equal *)
       if clearly_subtype_typ env (ntyp_of_vtyp ck) inf
       then None
       else Some inf

  let checking_type = function
    | Checking t -> t
    | Inference _ -> tcons (Top, Location.noloc)
    | Transparent r -> ntyp_of_vtyp r.checking

  let inferred env ~loc mode ty =
    match mode with
    | Inference r ->
       r := join_ptyp env !r ty
    | Checking ck ->
       subtype env ty ck |> or_raise `Expr loc
    | Transparent ({checking; inference} as r) ->
       subtype env ty (ntyp_of_vtyp checking) |> or_raise `Expr loc;
       match inference with
       | None -> r.inference <- Some ty
       | Some ty' -> r.inference <- Some (join_ptyp env ty' ty)
end

type ty_mode = Mode.t
let checking = Mode.checking
let inferring = Mode.inferring

type inspect_result =
  | Imatches of (ptyp, ntyp) Cons1.t loc
  (* FIXME: add Ifailed for when a Cons clearly does not match? *)
  | Iother

let inspect_cons' cons ty =
  match ty with
  | Tsimple _ ->
     (* bidirectional checking does not look inside Tsimple *)
     Iother
  | Tpoly _ ->
     (* FIXME: maybe make this impossible? *)
     Iother
  (* FIXME: multiple compatible cons? *)
  | Tcvj ([c,cloc],[],_loc) ->
     (match Cons1.sub_head cons c with Le _ -> Imatches (c,cloc) | Un _ -> Iother)
  | _ -> Iother

let inspect_cons cons ty = inspect_cons' cons (Mode.checking_type ty)

let inspect_poly_func env params ty =
  let poly, ty =
    match Mode.checking_type ty with
    | Tpoly {vars; body} ->
       (* rigvars not in scope in body, so no rig_names *)
       let env', open_rvs = enter_rigid env vars SymMap.empty in
       (* FIXME: Can there be flexvars used somewhere? Do they get bound/hoisted properly? *)
       Some (vars, env'), open_rvs body
    | ty -> None, ty
  in
  match inspect_cons' (Cons1.Func (params, ())) ty with
  | Imatches (Func (ptypes, rtype), _) ->
     Some (poly, ptypes, rtype)
  | _ ->
     None

let typ_of_tyexp env ty =
  Check_type.typ_of_tyexp ~lookup:Check_type.default_lookup_fn ~env ty

let mk_action (act : _ Check_pat.action) body : Elab.typed_action =
  let act_bindings, act_comp_bindings =
    match act.bindings with
    | None -> SymMap.empty, `Unused
    | Some {bindings; shared_cont = sc} ->
       SymMap.map (fun vb -> elab_ptyp vb.typ, vb.comp_var) bindings,
       match sc with
       | None -> `Once
       | Some sc -> `Shared sc
  in
  { act_body = body;
    act_bindings;
    act_comp_bindings }

let rec check env ~(mode : generalisation_mode) e (ty : ty_mode) : typed_exp =
  Mode.wf env ty;
  match e with
  | None, loc -> fail loc Syntax
  | Some e, loc ->
     let e = check' env ~mode loc e ty in
     Some e, loc

(* FIXME: default is to infer & subtype, but we probably shouldn't
   even attempt this on intro forms at the wrong type. e.g. checking
   (1,2) against int *)
and check' env ~mode eloc (e : exp') ty : typed_exp' =
  let inferred inf = Mode.inferred env ~loc:eloc ty inf in
  match e with
  | Lit l ->
     let lty, e = infer_lit l in
     inferred lty;
     e

  | Var (id, loc) ->
     begin match Env.lookup_value env id with
     | None -> fail loc (Bad_name (`Unknown, `Var, id.label))
     | Some v ->
        mark_var_use_at_level ~mode v.gen_level;
        inferred v.typ;
        Var ((id,loc), v.comp_var)
     end

  | Typed (e, ty) ->
     let t = Check_type.typ_of_tyexp ~lookup:Check_type.default_lookup_fn ~env ty in
     inferred t;
     let e = check env ~mode e (checking t) in
     Typed (e, elab_ptyp t)

  | If ((_,loc) as e, ifso, ifnot) ->
     let e = check env ~mode e (checking (tcons (c_bool loc))) in
     (* FIXME: probably broken for Transparent checking against non-simple types
        (since the join might make the inferred type not a subtype of checked?)*)
     let ifso = check env ~mode ifso ty in
     let ifnot = check env ~mode ifnot ty in
     If (e, ifso, ifnot)

  | Tuple (tag, fields) ->
     let cons_fail err cploc (cn,cnloc) =
       let fields =
         Exp.record_fields ~loc:eloc fields
         |> List.map (fun ((f,loc),_,_e) -> f, Fields.Fpresent ((),loc))
         |> Fields.of_list
       in
       (* drop tag to avoid making invalid args *)
       let tag = match tag with Some Anon_tag -> tag | _ -> None in
       let cp = Cons1.Record {tag; args=[]; body=fields} in
       let err = make_err env err (cp, cploc) (cn, cnloc) in
       fail eloc (Conflict (`Expr, err))
     in
     let cons_fail_field (err : Fields.field_error) cn =
       let err, cploc, cnloc =
         match err with
         | Field_missing (name, ploc, nloc) ->
            Field_missing name, ploc, nloc
         | Field_extra (name, ploc, nloc) ->
            Field_extra name, ploc, nloc
       in
       cons_fail err cploc (cn, cnloc)
     in

     (* expand punned fields *)
     let fields =
       Exp.record_fields ~loc:eloc fields
       |> List.map (fun ((f,floc), m, e) ->
         if m = Optional then fail floc (Bad_tuple_intro `Opt);
         let e = match f, e with
           | _, Some e -> e
           | Field_positional _, None -> fail floc Syntax
           | Field_named k, None -> (Some (Exp.Var ({label=k; shift=0}, floc)), floc) in
         (f, floc), e, ref None)
     in

     (* inspect checked type *)
     let tag, fields =
       let orig_fields = fields in
       let fields = Fields.of_list (List.map (fun ((f,loc), _, r) -> f, Fields.Fpresent (r, loc)) fields) in
       let matching_conses ~tag conses =
         conses |> List.filter_map (fun ((cons : _ Cons1.t),consloc) ->
           match tag, cons with
           | Some tag, Record ({tag=None; _} as r) ->
              Some (tag, consloc, r)
           | None, Record ({tag=Some tag; _} as r) ->
              Some (tag, consloc, r)
           | Some tag, Record ({tag=Some tag'; _} as r)
                when Cons1.tuple_tag_equal tag tag' ->
              Some (tag, consloc, r)
           | _ -> None)
       in
       let get_matching_cons ((conses, rvs, tyloc) : _ tcvj) =
         match matching_conses ~tag conses with
         | [p] -> p
         | _ ->
            (* FIXME: factor this out into types.ml somewhere *)
            let err =
              match
                List.map (fun (tag,_,_) -> tag) (matching_conses ~tag:None conses)
              with
              | [] -> Cons1.Incompatible
              | tags -> (Cons1.Expected_tag (tag, tags))
            in
            let tunit _ = Tsimple () in
            let body = Fields.map fields ~pos:tunit in
            let cp = tcons (Cons1.Record {tag; args=[]; body}, eloc) in
            let ty =
              let conses = List.map (fun (c,l) -> Cons1.map ~neg:tunit ~pos:tunit c, l) conses in
              (conses, rvs, tyloc)
            in
            let err = make_err' env (Head err) (cp,eloc) (Tcvj ty, Option.value tyloc ~default:eloc) in
            fail eloc (Conflict (`Expr, err))
       in
       let expander ~loc ~args (tag : tuple_tag option) =
         match tag with
         | None ->
            fun _ -> Fields.Funknown loc
         | Some (Struct_tag _ | Anon_tag) ->
            fun _ -> Fields.Fabsent loc
         | Some (Named_tag tag) ->
            let decl_fields = Env.get_decl_fields env (fst tag) in
            fun fn ->
            Fields.find fn (decl_fields,())
            |> Option.value ~default:(Fields.Fabsent loc)
            |> Fields.field_desc_map (fun ty ->
              let neg ty vars =
                let (t, _) = List.nth args (as_single_var ty vars) in t
              in
              let pos ty vars =
                let (_, t) = List.nth args (as_single_var ty vars) in t
              in
              open_typ ~neg ~pos 0 (gen_zero ty))
       in
       let check_tag = function
         | Anon_tag | Struct_tag _ as t -> t
         | Named_tag (s,sloc) as t ->
            match Env.lookup_decl env s with
            | Some {name=_; params=_; body = Decl_record _} -> t
            | _ -> fail sloc (Bad_name (`Unknown, `Type, s))
       in

       let check_fields ~loc ~mode_fn (record : _ Cons1.cons_record) =
         begin match
           Fields.sub
             (fields, fun _ -> Fabsent eloc)
             (record.body, expander ~loc ~args:record.args record.tag)
             ~f:(fun _fn r ty -> r := Some (mode_fn ty))
         with
         | Ok () -> ()
         | Error err ->
            cons_fail_field err (Cons1.Record record)
         end;
         orig_fields |> List.map (fun (f, e, ty) ->
           match !ty with
           | Some ty ->
              f, check env ~mode e ty
           | None ->
              let ty = inferring () in
              let e = check env ~mode e ty in
              f, (Some (Typed (e, elab_ptyp (Mode.inferred_type env ty))), snd e))
       in
       match ty with
       | Checking (Tcvj conses as tcheck) when not (is_ttop tcheck) ->
          let tag, consloc, record = get_matching_cons conses in
          let typed_fields = check_fields ~loc:consloc ~mode_fn:Mode.checking record in
          tag, typed_fields
       | Transparent ({checking=(Tcvj conses); _} as r)
            when not (is_ttop r.checking) ->
          let tag, consloc, record = get_matching_cons conses in
          let typed_fields = check_fields ~loc:consloc ~mode_fn:Mode.transparent record in
          let () =
            let body =
              Fields.filter_map ~pos:(fun r -> Mode.transparent_inferred_type env (Option.get !r)) fields
            in
            let args = List.map (fun (n,p) -> ntyp_of_vtyp n, ptyp_of_vtyp p) record.args in
            let cons = Cons1.Record {tag = Some tag; args; body} in
            Mode.inferred env ~loc:eloc ty (tcons (cons, eloc))
          in
          tag, typed_fields
       | _ ->
          (* FIXME: do a subtyping check with the least record beforehand? *)
          match tag with
          | None -> fail eloc (Bad_tuple_intro (`Tag (tag, [])))
          | Some (Anon_tag | Struct_tag _ as tag) ->
             let field_tys = Fields.map ~pos:(fun r -> let ty = inferring () in r := Some ty; ty) fields in
             let typed_fields = List.map (fun (f, e, ty) -> f, check env ~mode e (Option.get !ty)) orig_fields in
             let () =
               let body = Fields.map ~pos:(Mode.inferred_type env) field_tys in
               let cons = Cons1.Record {tag = Some tag; args=[]; body} in
               Mode.inferred env ~loc:eloc ty (tcons (cons, eloc))
             in
             tag, typed_fields
          | Some (Named_tag t as tag) ->
             let _tag = check_tag tag in
             let decl_params = Env.get_decl_params env (fst t) in
             let args : (vtyp,vtyp) Cons1.tyarg list =
               (* FIXME: args? *)
               decl_params |> List.map (fun (var, _) ->
                 let fv = fresh_flexvar (Env.level env) in
                 (match var.occurs_neg with `No -> tbot None | `Yes -> Tsimple fv),
                 (match var.occurs_pos with `No -> ttop Location.noloc | `Yes|`Strict -> Tsimple fv))
             in
             let record : _ Cons1.cons_record = { tag = Some tag; args; body = Fields.empty } in
             let typed_fields = check_fields ~loc:(snd t) ~mode_fn:Mode.transparent record in
             let () =
               let body =
                 Fields.filter_map ~pos:(fun r -> Mode.transparent_inferred_type env (Option.get !r)) fields
               in
               let args =
                 args |> List.map (fun (n,p) -> ntyp_of_vtyp n, ptyp_of_vtyp p)
               in
               let cons = Cons1.Record {tag=Some tag; args; body} in
               Mode.inferred env ~loc:eloc ty (tcons (cons, eloc))
             in
             tag, typed_fields
     in
     Tuple (tag, fields)

  | Proj (e, (field, loc)) ->
     let ty, e = infer env ~mode e in
     let f = Field_named field in
     let r = ref (tbot None) in
     let tyf =
       match
        match_ptyp ~loc:eloc env ty
         [Record { tag = None;
                   args = []; (* FIXME *)
                   body = {
                       fields = FieldMap.singleton f (Fields.Fpresent (r, loc));
                       fnames = [Field_named field]} }]
       with
       | Ok () -> !r
       | Error c -> fail eloc (Conflict (`Expr, c)) in
     inferred tyf;
     Proj (e, (field, loc))

  | Let (p, pty, rhs, body) ->
     let pty, e, gen_level = check_rhs env ~mode pty rhs in

     let case : case = ([[p]], snd p), body in
     let act, split = Check_pat.split_cases ~matchloc:(snd p) env [pty, gen_level] [case] in
     let act = Util.as_singleton act in
     let env = extend_env env act in
     let body = check env ~mode body ty in
     Let (p, split, elab_ptyp pty, e, mk_action act body)

  | Seq (e1, e2) ->
     let e1 = check env ~mode e1 (checking (unit eloc)) in
     let e2 = check env ~mode e2 ty in
     Seq (e1, e2)

  | Fn ((poly, params, ret, body) as fndef) ->
     begin match poly, lazy (inspect_poly_func env params ty) with
     | None, lazy (Some (typoly, ptypes, rtype)) ->
        let poly, env =
          match typoly with
          | Some (vars, env) ->
             let poly = (IArray.map (function (_,None) as b -> b | (s, Some t) -> s, Some (Elab_ptyp t)) vars) in
             Some poly, env
          | None -> None, env
        in
          let param_list =
            List.map2 (fun (pat, pty) ty ->
              let ty_level =
                match pty with
                | None -> ty, Some (Env.level env)
                | Some pty ->
                   let t = Check_type.typ_of_tyexp ~lookup:Check_type.default_lookup_fn ~env pty in
                   subtype env ty t |> or_raise `Pat (snd pty);
                   t, None
              in
              pat, ty_level
            ) params ptypes
          in
          let param_ptyps = List.map (fun (_p, tl) -> tl) param_list in
          let case : case =
            ([List.map (fun (p, _tl) -> p) param_list], eloc), body
          in
          let act, split =
            Check_pat.split_cases ~matchloc:eloc env param_ptyps [case] in
          let act = Util.as_singleton act in

          let env' = extend_env env act in
          let ret_type =
            match ret with
            | None -> rtype
            | Some ty' ->
               let t = typ_of_tyexp env' ty' in
               subtype env' t rtype |> or_raise `Subtype (snd ty');
               t
          in
          let body = check env' ~mode body (checking ret_type) in
          (* FIXME: is this wrong? What if the annotations names have changed? *)
          let fndef =
            match poly with
            | None ->
               (* FIXME: keep type annotations here too? *)
               (None,
                List.map (fun (p, _) -> p, None) params,
                split,
                None (*FIXME ret_type?*),
                mk_action act body)
            | Some poly ->
               let fndef : typed_func_def =
                 (None,
                  List.map2 (fun (p, _) ty -> p, Some (elab_ptyp ty)) params ptypes,
                  split,
                  Some (Elab_ntyp rtype) (*FIXME ret_type?*),
                  mk_action act body)
               in
               let close ~ext t =
                 close_typ ~neg:ignore ~pos:ignore (Env.level env) (List.length ext) t in
               let (_, params, psplit, ret, body) = typed_map_func_def ~neg:close ~pos:close ~ext:[] fndef in
               (Some poly, params, psplit, ret, body)
          in
          Fn fndef
       | _, _ ->
          let ty, tfndef = infer_func_def env ~loc:eloc ~mode eloc fndef in
          inferred ty;
          Fn tfndef
     end

  | FnDef ((s, sloc), fndef, body) ->
     let fmode = fresh_gen_mode () in
     let fty, tfndef = infer_func_def env ~loc:sloc ~mode:fmode eloc fndef in
     mark_var_use_at_level ~mode fmode.gen_level_acc;
     let cvar = IR.Binder.fresh ~name:s () in
     let binding = {typ = fty; gen_level = fmode.gen_level_acc; comp_var = IR.Binder.ref cvar} in
     let env = Env.extend_vals env ~vals:(SymMap.singleton s binding) in
     let body = check env ~mode body ty in
     FnDef((s,sloc), cvar, tfndef, body)

  | App (f, args) ->
     let fty, f = infer env ~mode f in
     let tyargs = List.map (fun _ -> ref (tcons (Top, Location.noloc))) args in
     let tyret = ref (tbot None) in
     let () =
       match match_ptyp ~loc:eloc env fty [Func (tyargs, tyret)] with
       | Ok () -> ()
       | Error e -> fail eloc (Conflict (`Expr, e)) in
     (* FIXME: don't ignore param names *)
     let args = List.map2 (fun (_,e) t -> check env ~mode e (checking !t)) args tyargs in
     inferred !tyret;
     App (f, args)

  | Match ((es, matchloc), cases) ->
     (* FIXME: maybe check sometimes? *)
     let es = List.map (infer env ~mode) es in
     (* FIXME is this the right gen_level? How does this work again? *)
     let gen_level = mode.gen_level_acc in
     let etyps, es = List.map (fun (t, _) -> t, gen_level) es, List.map snd es in
     let actions, split = Check_pat.split_cases ~matchloc env etyps cases in
     let actions =
       List.map2 (fun act (_, exp) ->
         let env = extend_env env act in
         (mk_action act (check env ~mode exp ty)))
         actions cases
     in
     Match ((es, matchloc),
            split,
            List.map2 (fun (ps,_) e -> ps, e) cases actions)

  | Pragma ("true"|"false" as b) when match inspect_cons (fst (c_bool eloc)) ty with Imatches (Record _,_) -> true | _ -> false ->
     Pragma b
  | Pragma "bot" ->
     inferred (tbot (Some eloc));
     Pragma "bot"
  | Pragma s -> failwith ("pragma: " ^ s)


and infer env ~(mode : generalisation_mode) (e : exp) : ptyp * typed_exp =
  let ty_mode = Mode.inferring () in
  let e = check env ~mode e ty_mode in
  Mode.inferred_type env ty_mode, e

and infer_func_def env ~loc ~mode eloc (poly, params, ret, body) : ptyp * typed_func_def =
   let ty, typed_poly, _generalised, (act, split) =

  let rigvars', rig_names =
    match poly with
    | None -> IArray.empty, SymMap.empty
    | Some poly -> Check_type.enter_polybounds ~lookup:Check_type.default_lookup_fn ~env poly in

  let env', _rigvars = enter_rigid env rigvars' rig_names in
  let check_ty ~ispos ty =
    let ty = typ_of_tyexp env' ty in
    (* check for contravariant joins *)
    begin try ignore (close_typ_poly_exn ~ispos (Env.level env') ty)
    with Types.CloseError (err,loc) ->
      let loc = Option.value loc ~default:eloc in
      fail loc (Illformed_type (`Close_error err))
    end;
    ty
  in
  let orig_ty, typed_exp, gen_level, act, split =
    let params = List.map (fun (p, ty) ->
      match ty with
      | Some ty ->
         let ty = check_ty ~ispos:false ty in
         (ty,ty), p, None
      | None ->
         fresh_flow env', p, Some (Env.level env')) params in
    let param_ptyps = List.map (fun (((_tn, tp), _p, gen_level)) -> tp, gen_level) params in
    let case : case =
      ([List.map (fun ((_ty, p, _lvl)) -> p) params], eloc), body in
    let act, split = Check_pat.split_cases ~matchloc:eloc env' param_ptyps [case] in
    let act = Util.as_singleton act in
    let env' = extend_env env' act in

    let bmode = fresh_gen_mode () in
    let res, body =
      match ret with
      | Some ty ->
         let ty = check_ty ~ispos:true ty in
         ty, check env' ~mode:bmode body (checking ty)
      | None ->
         infer env' ~mode:bmode body in
    let _ = List.map (fun ((tn,tp),_,_) -> wf_ntyp env' tn; wf_ptyp env' tp) params in
    (* FIXME params or ptys? What happens if they disagree? *)
    tcons (Func (List.map (fun ((tn,_tp),_,_) -> tn) params, res), eloc),
    body,
    bmode.gen_level_acc,
    act,
    split
  in
  wf_ptyp env' orig_ty;
  wf_typed_exp env' typed_exp;
  let can_generalise =
    match gen_level with
    | None -> true
    | Some lvl when Env_level.equal lvl (Env.level env') -> true
    | lvl ->
       mark_var_use_at_level ~mode lvl;
       false
  in
  let policy = if can_generalise then `Generalise loc else `Hoist env in
  let act = mk_action act typed_exp in
  let bvars, (ty, act) =
    try Promotion.promote_exn ~policy ~rigvars:rigvars' ~env:env' (orig_ty, act)
    with Types.CloseError (err,errloc) ->
      (* FIXME: locations and explanations here are poor *)
      let loc = Option.value errloc ~default:loc in
      fail loc (Illformed_type (`Close_error err))
  in
  if Array.length bvars = 0 then
    ty, None, can_generalise, (act, split)
  else
    let next_name = ref 0 in
    let rec mkname () =
      let n = !next_name in
      incr next_name;
      let name = match n with
        | n when n < 26 -> Printf.sprintf "%c" (Char.chr (Char.code 'a' + n))
        | n -> Printf.sprintf "t_%d" (n-26) in
      (* NB: look up env', to ensure no collisions with rigvars *)
      match Typedefs.env_lookup_type_var env' Location.noloc name with
      | None -> name, Location.noloc
      | Some _ -> mkname () in
    let bounds = bvars
      |> Array.map (function
        | Gen_rigid rv -> IArray.get rigvars' rv.var
        | Gen_flex r when is_ttop r -> mkname (), None
        | Gen_flex r -> mkname (), Some r)
      |> IArray.of_array in
    let tpoly = Tpoly { vars = bounds; body = ty } in
    wf_ptyp env tpoly;
    tpoly,
    (Some (IArray.map (function (_,None) as b -> b | (s, Some t) -> s, Some (Elab_ntyp t)) bounds)),
    can_generalise,
    (act, split)
   in
   let tparams, tret =
     (* FIXME awful hack *)
     match ty with
     | Tcvj ([Func (t,r),_], [], _loc)
     | Tpoly { body = Tcvj ([Func (t,r),_],[], _loc); _ } -> t,r
     | _ -> intfail "wuh?"
   in
   let params = List.map2 (fun (p, _) t -> (p, Some (Elab_ntyp t))) params tparams in
   ty,
   (typed_poly,
    params,
    split,
    Some (Elab_ptyp tret),
    act)

and extend_env env act =
  let vals = (Option.get act.Check_pat.bindings).bindings in
  Env.extend_vals env ~vals

and infer_lit = function
  | l, loc ->
     infer_lit' loc l,
     Lit (l, loc)
and infer_lit' loc = function
  | Bool _ -> tcons (c_bool loc)
  | Int _ -> tcons (c_int loc)
  | String _ -> tcons (c_string loc)

and check_rhs env ~mode pty e =
  match pty with
  | None ->
     let bmode = fresh_gen_mode () in
     let pty, e = infer env ~mode:bmode e in
     mark_var_use_at_level ~mode bmode.gen_level_acc;
     pty, e, bmode.gen_level_acc
  | Some ty ->
     let t = typ_of_tyexp env ty in
     t, check env ~mode e (checking t), None
