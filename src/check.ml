open Util
open Tuple_fields
open Exp
open Typedefs
open Types
open Error

let rec env_lookup_var env v =
  match env with
  | Env_nil -> Error (Bad_name (`Unknown, `Var, v.label))
  | Env_vals { vals = vs; rest; _ }
       when SymMap.mem v.label vs ->
     if v.shift = 0 then Ok (SymMap.find v.label vs) else
       env_lookup_var rest { v with shift = v.shift - 1 }
  | Env_types { rest; _ } | Env_vals {rest; _}->
     env_lookup_var rest v

let env_lookup_type_var env lvl loc name =
  match env_lookup_type_var env loc name with
  | Some v ->
     if not (Env_level.extends v.level lvl) then
       Error (Illformed_type (`Bound_crosses_levels name))
     else
       Ok v
  | None -> Error (Bad_name (`Unknown, `Type, name))

let syn_tjoin loc (a : (_, _) typ) (b : (_, _) typ) =
  let rec check_cons cons = function
    | Tjoin (a, b, _loc) -> check_cons cons a; check_cons cons b
    | Tsimple _ -> intfail "syn_tjoin: Tsimple"
    | Tvar _ -> ()
    | Tbot _ -> fail loc (Illformed_type `Join_multi_cons)
    | Tcons (c, _) ->
       if not (Cons1.incomparable_head c cons) then
         fail loc (Illformed_type `Join_multi_cons)
    | Tpoly _ ->
       fail loc (Illformed_type `Join_poly)
  in
  let rec check_join p = function
    | Tjoin (a, b, _) -> check_join p a; check_join p b
    | Tsimple _ -> intfail "syn_tjoin: Tsimple"
    | Tvar _ -> ()
    | Tbot _ -> fail loc (Illformed_type `Join_multi_cons)
    | Tcons (c, _) -> check_cons c p
    | Tpoly _ ->
       fail loc (Illformed_type `Join_poly)
  in
  check_join a b;
  Tjoin (a, b, Some loc)

let tcons loc cons = Tcons (cons, loc)

let rec typ_of_tyexp : 'a 'b . env -> Env_level.t -> tyexp -> ('a, 'b) typ =
  fun env lvl ty -> match ty with
  | None, loc -> fail loc Syntax
  | Some t, loc -> typ_of_tyexp' env lvl loc t
and typ_of_tyexp' : 'a 'b . env -> Env_level.t -> Location.t -> tyexp' -> ('a, 'b) typ =
  fun env lvl loc ty -> match ty with
  | Tnamed (name, _) ->
     (* FIXME shifting? *)
     let name = name.label in
     begin match lookup_named_type loc name with
     | Some t -> t
     | None ->
        match env_lookup_type_var env lvl loc name with
        | Ok v -> Tvar (Vrigid v)
        | Error e -> fail loc e
     end
  | Trecord (tag, fields) ->
     tcons loc (Record (Option.map fst tag, typs_of_tuple_tyexp env lvl fields))
  | Tfunc (args, res) ->
     tcons loc (Func (List.map (typ_of_tyexp env lvl) args, typ_of_tyexp env lvl res))
  | Tjoin (a, b) ->
     syn_tjoin loc (typ_of_tyexp env lvl a) (typ_of_tyexp env lvl b)
  | Tforall (vars, body) ->
     let vars, name_ix = enter_polybounds env vars in
     let env, _rigvars = enter_rigid env vars name_ix in
     let body = close_typ_rigid ~ispos:true (env_level env) (typ_of_tyexp env (env_level env) body) in
     Tpoly { vars; body }

and typs_of_tuple_tyexp : 'a 'b . env -> Env_level.t -> tyexp tuple_fields -> ('a, 'b) typ tuple_fields =
  fun env lvl ts -> map_fields (fun _fn t -> typ_of_tyexp env lvl t) ts

and enter_polybounds : 'a 'b . env -> typolybounds -> (string Location.loc * ('a,'b) typ option) iarray * int SymMap.t =
  fun env vars ->
  let name_ix =
    vars
    |> List.mapi (fun i ((n, l), _bound) -> i, l, n)
    |> List.fold_left (fun smap ((i : int), loc, n) ->
      if SymMap.mem n smap then fail loc (Bad_name (`Duplicate, `Type, n));
      SymMap.add n i smap) SymMap.empty in
  let level = Env_level.extend (env_level env) in
  let stubs =
    vars
    |> List.map (fun (name,_) -> {name; upper=[Top]})
    |> IArray.of_list in
  let mkbound rig_names _loc bound =
    match bound with
    | None -> None
    | Some b ->
       let temp_env = Env_types { level; rig_names; rig_defns = stubs; rest = env } in
       let bound = close_typ_rigid ~ispos:false level (typ_of_tyexp temp_env (env_level temp_env) b) in
       (* FIXME: Tcons / Tjoin *)
       begin match bound with Tcons _ -> () | _ -> fail (snd b) (Illformed_type `Bound_not_cons) end;
       if not (check_simple bound) then fail (snd b) (Illformed_type `Bound_not_simple);
       Some bound
  in
  let name_ix, vars = IArray.map_fold_left (fun names ((name',loc) as name, bound) ->
    let names' = SymMap.add name' (SymMap.find name' name_ix) names in
    names', (name, mkbound names loc bound)) SymMap.empty (IArray.of_list vars) in
  vars, name_ix

let typ_of_tyexp env t = typ_of_tyexp env (env_level env) t

let unit loc = tcons loc (Record (None, Tuple_fields.collect_fields []))

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


let elab_gen (env:env) ~loc ~mode poly (fn : env -> ptyp * typed_exp * env_level option * 'rest) : ptyp * (typed_polybounds option * typed_exp) * bool * 'rest =
  let rigvars', rig_names =
    match poly with
    | None -> IArray.empty, SymMap.empty
    | Some poly -> enter_polybounds env poly in

  let env', _rigvars = enter_rigid env rigvars' rig_names in
  let orig_ty, typed_exp, gen_level, rest = fn env' in
  wf_ptyp env' orig_ty;
  let can_generalise =
    match gen_level with
    | None -> true
    | Some lvl when Env_level.equal lvl (env_level env') -> true
    | lvl ->
       mark_var_use_at_level ~mode lvl;
       false
  in
  let map ~neg ~pos (ty, typed_exp) =
    let ty = pos ~mode:`Poly ~index:0 ty in
    let typed_exp = typed_map_typs_exp typed_exp ~index:0
                ~neg:(neg ~mode:`Elab)
                ~pos:(pos ~mode:`Elab)
    in
    (ty, typed_exp)
  in
  let policy = if can_generalise then `Generalise loc else `Hoist env in
  let bvars, (ty, typed_exp) = promote ~policy ~rigvars:rigvars' ~env:env' ~map (orig_ty, typed_exp) in
  if Vector.length bvars = 0 then
    ty, (None, typed_exp), can_generalise, rest
  else
    let next_name = ref 0 in
    let rec mkname () =
      let n = !next_name in
      incr next_name;
      let name = match n with
        | n when n < 26 -> Printf.sprintf "%c" (Char.chr (Char.code 'A' + n))
        | n -> Printf.sprintf "T_%d" (n-26) in
      (* NB: look up env', to ensure no collisions with rigvars *)
      match env_lookup_type_var env' (env_level env') Location.noloc name with
      | Error _ -> name, Location.noloc
      | Ok _ -> mkname () in
    let bounds = bvars |> Vector.to_array |> Array.map (function Gen_rigid rv -> IArray.get rigvars' rv.var | Gen_flex r -> mkname (), Some r) |> IArray.of_array in
    let tpoly = Tpoly { vars = bounds; body = ty } in
    wf_ptyp env tpoly;
    tpoly,
    (Some bounds, typed_exp),
    can_generalise,
    rest

(* FIXME:
   This improves elaborations but is a bit of a hack.
   Decide whether to keep it! *)
let elab_ptyp = function
  | Tsimple [Lflexvar v] -> Elab_ntyp (Tsimple v)
  | ty -> Elab_ptyp ty
  
let fresh_flow env =
  let fv = fresh_flexvar (env_level env) in
  Tsimple fv, Tsimple (of_flexvar fv)

type ty_mode =
  | Checking of ntyp
  | Inference of ptyp ref

let inspect_poly = function
  | Checking (Tpoly p) -> Some p
  | _ -> None

type inspect_result =
  | Imatches of (ptyp, ntyp) Cons1.t
  (* FIXME: add Ifailed for when a Cons clearly does not match? *)
  | Iother

let inspect_cons cons = function
  | Checking (Tsimple _) ->
     (* bidirectional checking does not look inside Tsimple *)
     Iother
  | Checking (Tpoly _) ->
     (* FIXME: maybe make this impossible? *)
     Iother
  (* FIXME: Tcons/Tjoin selection *)
  | Checking (Tcons (c,_loc)) ->
     (match Cons1.sub_head cons c with Le _ -> Imatches c | Un _ -> Iother)
  | Checking (Tbot _ | Tvar _ | Tjoin _) | Inference _ -> Iother

let rec check env ~(mode : generalisation_mode) e (ty : ty_mode) : typed_exp =
  (match ty with
   | Checking ty -> wf_ntyp env ty
   | Inference _ -> ());
  match e with
  | None, loc -> fail loc Syntax
  | Some e, loc ->
     let e = check' env ~mode loc e ty in
     Some e, loc

(* FIXME: default is to infer & subtype, but we probably shouldn't
   even attempt this on intro forms at the wrong type. e.g. checking
   (1,2) against int *)
and check' env ~mode eloc (e : exp') ty : typed_exp' =
  let inferred inf =
    match ty with
    | Checking ty ->
       subtype env inf ty |> or_raise `Expr eloc
    | Inference slot ->
       slot := join_ptyp env !slot inf
  in
  match e with
  | Lit l ->
     let lty, e = infer_lit l in
     inferred lty;
     e

  | Var (id, loc) ->
     begin match env_lookup_var env id with
     | Ok v ->
        mark_var_use_at_level ~mode v.gen_level;
        inferred v.typ;
        Var ((id,loc), v)
     | Error e -> fail loc e
     end

  | Typed (e, ty) ->
     let t = typ_of_tyexp env ty in
     inferred t;
     let e = check env ~mode e (Checking t) in
     Typed (e, elab_ptyp t)

  | If (e, ifso, ifnot) ->
     let e = check env ~mode e (Checking (tcons (snd e) Bool)) in
     let ifso = check env ~mode ifso ty in
     let ifnot = check env ~mode ifnot ty in
     If (e, ifso, ifnot)

  | Tuple (tag, fields) ->
     if fields.fopen = `Open then failwith "invalid open tuple ctor";
     let target_ty = Cons1.Record(Option.map fst tag,
                            map_fields (fun _ _ -> ()) fields) in
     let fields =
       (* FIXME: simplify here? *)
       match inspect_cons target_ty ty with
       | Imatches (Record (_, tf)) ->
          let infer_typed env ((_,loc) as e) =
            let ty, e = infer env ~mode e in
            Some (Typed (e, elab_ptyp ty)), loc
          in
          merge_fields fields tf
            ~both:(fun _fn e ty -> Some (check env ~mode e (Checking ty)))
            ~left:(fun _fn e -> Some (infer_typed env e))
            ~right:(fun fn _ty -> failwith ("missing " ^ string_of_field_name fn) )
            ~extra:(function
              | _, (`Closed, `Extra) -> failwith "extra"
              | (`Open, _), _ -> failwith "invalid open tuple ctor" (* no open tuples *)
              | (`Closed, `Extra), _ -> failwith "missing"
              | _ -> `Closed)
       | _ ->
          let fields = map_fields (fun _fn e -> infer env ~mode e) fields in
          inferred (tcons eloc (Record (Option.map fst tag,
                                        map_fields (fun _ (ty, _e) -> ty) fields)));
          map_fields (fun _fn (_ty, e) -> e) fields
     in
     Tuple(tag, fields)

  | Proj (e, (field, loc)) ->
     let ty, e = infer env ~mode e in
     let f = Field_named field in
     let (), tyf =
       match
        match_typ env ty eloc
         (Record (None,
                  { fields = FieldMap.singleton f ();
                   fnames = [Field_named field]; fopen = `Open }))
       with
       | Ok (Record (_, r)) -> FieldMap.find f r.fields
       | Ok _ -> assert false
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
     Let (p, split, elab_ptyp pty, e, { act with rhs = body })

  | Seq (e1, e2) ->
     let e1 = check env ~mode e1 (Checking (unit eloc)) in
     let e2 = check env ~mode e2 ty in
     Seq (e1, e2)

  (* FIXME should I combine Tpoly and Func? *)
  | Fn ((poly, params, ret, body) as fndef) ->
     begin match inspect_poly ty with
     | Some {vars; body} ->
        (* rigvars not in scope in body, so no rig_names *)
        let env', open_rigvars = enter_rigid env vars SymMap.empty in
        let body = open_rigvars body in
        check' env' ~mode eloc e (Checking body)
        (* FIXME: Can there be flexvars used somewhere? Do they get bound/hoisted properly? *)
     | None ->
        let target_ty = Cons1.Func (List.map (fun (k,_) -> k,()) params, ()) in
        match poly, inspect_cons target_ty ty with
       | None, Imatches (Func (ptypes, rtype)) ->
          (* If poly <> None, then we should infer & subtype *)
          (* FIXME: do we need another level here? Does hoisting break things? *)
          let param_list =
            List.map2 (fun (pat, pty) ty ->
              let ty_level =
                match pty with
                | None -> ty, Some (env_level env)
                | Some pty ->
                   let t = typ_of_tyexp env pty in
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
          let body = check env' ~mode body (Checking ret_type) in
          (* FIXME: is this wrong? What if the annotations names have changed? *)
          (* FIXME: insert / keep type annotations? *)
          Fn (None, List.map (fun (p, _) -> p, None) params, split, None (*FIXME ret_type?*), {act with rhs = body })
       | _ ->
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
     let env = Env_vals { vals = SymMap.singleton s binding; rest = env } in
     let body = check env ~mode body ty in
     FnDef((s,sloc), cvar, tfndef, body)

  | App (f, args) ->
     let fty, f = infer env ~mode f in
     let tyargs, ((), tyret) =
       match
        match_typ env fty eloc (Func (args, ()))
       with
       | Ok (Func (a, r)) -> a, r
       | Ok _ -> assert false
       | Error e -> fail eloc (Conflict (`Expr, e)) in
     (* FIXME: don't ignore param names *)
     let args = List.map (fun ((_,e), t) -> check env ~mode e (Checking t)) tyargs in
     inferred tyret;
     App (f, args)

  | Match ((es, matchloc), cases) ->
     let es = List.map (infer env ~mode) es in
     (* FIXME is this the right gen_level? How does this work again? *)
     let gen_level = mode.gen_level_acc in
     let etyps, es = List.map (fun (t, _) -> t, gen_level) es, List.map snd es in
     let actions, split = Check_pat.split_cases ~matchloc env etyps cases in
     let actions =
       List.map2 (fun act (_, exp) ->
         let env = extend_env env act in
         { act with rhs = check env ~mode exp ty })
         actions cases
     in
     Match ((es, matchloc),
            split,
            List.map2 (fun (ps,_) e -> ps, e) cases actions)

  | Pragma ("true"|"false" as b) when match inspect_cons Bool ty with Imatches Bool -> true | _ -> false ->
     Pragma b
  | Pragma "bot" ->
     inferred (Tbot (Some eloc));
     Pragma "bot"
  | Pragma s -> failwith ("pragma: " ^ s)


and infer env ~(mode : generalisation_mode) (e : exp) : ptyp * typed_exp =
  let ty = ref (Tbot None) in
  let e = check env ~mode e (Inference ty) in
  wf_ptyp env !ty;
  !ty, e

and infer_func_def env ~loc ~mode eloc (poly, params, ret, body) : ptyp * typed_func_def =
   let ty, (typed_poly, typed_fn), _generalised, (act, split) =
     elab_gen env ~loc ~mode poly (fun env ->
       let params = List.map (fun (p, ty) ->
         match ty with
         | Some ty ->
            let ty = typ_of_tyexp env ty in
            (* check for contravariant joins *)
            ignore (close_typ_rigid ~ispos:false (env_level env) ty);
            (ty,ty), p, None
         | None ->
            fresh_flow env, p, Some (env_level env)) params in
       let param_ptyps = List.map (fun (((_tn, tp), _p, gen_level)) -> tp, gen_level) params in
       let case : case =
         ([List.map (fun ((_ty, p, _lvl)) -> p) params], eloc), body in
       let act, split = Check_pat.split_cases ~matchloc:eloc env param_ptyps [case] in
       let act = Util.as_singleton act in
       let env' = extend_env env act in

       let bmode = fresh_gen_mode () in
       let res, body =
         match ret with
         | Some ty ->
            let ty = typ_of_tyexp env ty in
            ignore (close_typ_rigid ~ispos:true (env_level env) ty);
            ty, check env' ~mode:bmode body (Checking ty)
         | None ->
            infer env' ~mode:bmode body in
       let _ = List.map (fun ((tn,tp),_,_) -> wf_ntyp env tn; wf_ptyp env tp) params in
       (* FIXME params or ptys? What happens if they disagree? *)
       tcons eloc (Func (List.map (fun ((tn,_tp),_,_) -> tn) params, res)),
       body,
       bmode.gen_level_acc,
       (act, split)) in
   let tparams, tret =
     (* FIXME awful hack *)
     match ty with
     | Tcons (Func (t,r), _loc)
     | Tpoly { body = Tcons (Func (t,r), _loc); _ } -> t,r
     (* FIXME Tjoin/Tcons *)
     | _ -> intfail "wuh?"
   in
   let params = List.map2 (fun (p, _) t -> (p, Some t)) params tparams in
   ty,
   (typed_poly,
    params,
    split,
    Some tret,
    { act with rhs = typed_fn })
 
and extend_env env act =
  let vals = (Option.get act.Check_pat.bindings).bindings in
  Env_vals { vals; rest = env }

and infer_lit = function
  | l, loc ->
     infer_lit' loc l,
     Lit (l, loc)
and infer_lit' loc = function
  | Bool _ -> tcons loc Bool
  | Int _ -> tcons loc Int
  | String _ -> tcons loc String

and check_rhs env ~mode pty e =
  match pty with
  | None ->
     let bmode = fresh_gen_mode () in
     let pty, e = infer env ~mode:bmode e in
     mark_var_use_at_level ~mode bmode.gen_level_acc;
     pty, e, bmode.gen_level_acc
  | Some ty ->
     let t = typ_of_tyexp env ty in
     t, check env ~mode e (Checking t), None
