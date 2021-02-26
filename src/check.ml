open Tuple_fields
open Exp
open Typedefs
open Types

let report = function
  | Incompatible -> failwith "incompat"
  | Missing k -> failwith ("missing " ^ string_of_field_name k)
  | Extra _ -> failwith ("extra")


let rec split_tjoin env cons vars rest =
  match rest with
  | [] -> cons, vars
  | (None, _) :: _ -> failwith "type syntax error"
  | (Some ty, _) as ty' :: rest ->
     match ty with
     | Tjoin (a, b) ->
        split_tjoin env cons vars (a :: b :: rest)
     | Tparen a ->
        split_tjoin env cons vars (a :: rest)
     | Tforall _ -> failwith "Tforall in join"
     | ty ->
        let as_var =
          match ty with
          | Tnamed (name, _) ->
             (* FIXME shifting? *)
             env_lookup_type_var env name.label
          | _ -> None in
        match as_var with
        | Some v -> split_tjoin env cons (v :: vars) rest
        | None ->
           match cons with
           | None -> split_tjoin env (Some ty') vars rest
           | Some _ -> failwith "multiple cons in join"
     

let rec typ_of_tyexp : 'a 'b . env -> tyexp -> ('a, 'b) typ =
  fun env ty -> match ty with
  | None, _ -> failwith "type syntax error"
  | Some t, _ -> typ_of_tyexp' env t
and typ_of_tyexp' : 'a 'b . env -> tyexp' -> ('a, 'b) typ =
  fun env ty -> match ty with
  | Tnamed (name, _) ->
     (* FIXME shifting? *)
     let name = name.label in
     begin match lookup_named_type name with
     | Some cons -> Tcons cons
     | None ->
        match env_lookup_type_var env name with
        | Some v -> Tvar (Vrigid v)
        | None -> failwith ("unknown type " ^ name)
     end
  | Trecord fields ->
     Tcons (Record (typs_of_tuple_tyexp env fields))
  | Tfunc (args, res) ->
     Tcons (Func (typs_of_tuple_tyexp env args, typ_of_tyexp env res))
  | Tparen t ->
     typ_of_tyexp env t
  | Tjoin (a, b) ->
     let cons, rigvars = split_tjoin env None [] [a;b] in
     let cons =
       match cons with
       | None -> Bot
       | Some c ->
          match typ_of_tyexp env c with
          | Tcons c -> c
          | _ -> failwith "Expected a constructed type" in
     tcons {cons; rigvars}
  | Tforall (vars, body) ->
     let vars, name_ix = enter_polybounds env vars in
     let level = Env_level.extend (env_level env) in
     let rigvars = IArray.mapi (fun var _ -> {level;var}) vars in
     let rig_defns = vars |> IArray.map (fun (name, bound) ->
       { name; upper = simple_ptyp_bound level (open_typ_rigid rigvars bound) }) in
     let env = Env_types { level; rig_names = name_ix; rig_defns; rest = env } in
     let body = close_typ_rigid level (typ_of_tyexp env body) in
     Tpoly { vars; body }

and typs_of_tuple_tyexp : 'a 'b . env -> tyexp tuple_fields -> ('a, 'b) typ tuple_fields =
  fun env ts -> map_fields (fun _fn t -> typ_of_tyexp env t) ts

and enter_polybounds : 'a 'b . env -> typolybounds -> (string * ('a,'b) typ) iarray * int SymMap.t =
  fun env vars ->
  let name_ix =
    vars
    |> List.mapi (fun i ((n, _), _bound) -> i, n)
    |> List.fold_left (fun smap ((i : int), n) ->
      if SymMap.mem n smap then failwith ("duplicate rigvar name " ^ n);
      SymMap.add n i smap) SymMap.empty in
  let level = Env_level.extend (env_level env) in
  let stubs =
    vars
    |> List.map (fun ((name,_),_) -> {name; upper={cons=Top;rigvars=[]}})
    |> IArray.of_list in
  let temp_env = Env_types { level; rig_names = name_ix; rig_defns = stubs; rest = env } in
  let mkbound bound =
    match bound with
    | None -> Tcons Top
    | Some b ->
       match close_typ_rigid level (typ_of_tyexp temp_env b) with
       | Tcons c -> Tcons c
       (* FIXME: some vjoin cases are also fine. Var even? *)
       | _ -> failwith "rig var bounds must be Tcons" in
  let vars = IArray.map (fun ((name,_), bound) -> name, mkbound bound) (IArray.of_list vars) in
  vars, name_ix

(*

open Elab

let elab_gen env (fn : env -> typ * 'a elab) : typ * (typolybounds option * 'a) elab =
  let level' = env_next_level env Esort_flexible in
  let env' = env_cons env level' (Eflexible {vars=Vector.create(); names=SymMap.empty}) in
  let ty, (Elab (erq, ek)) = fn env' in
  wf_typ Pos env' ty;
  (* FIXME hack *)
  let rq = Pair(erq, Typ (Pos, ty)) in
  let rq = try Type_simplification.remove_joins env' level' rq 
           with e ->  (*PPrint.ToChannel.pretty 1. 80 stderr PPrint.(pr_env env' ^^ hardline ^^ Elab.pr_elab_req rq); *)raise e in

  let envgc, envgc_level, rq = Type_simplification.garbage_collect env' level' rq in
  wf_elab_req envgc rq;
  match generalise envgc envgc_level with
  | None ->
     (* nothing to generalise *)
     wf_elab_req env rq;
     let erq, ty = match rq with Pair(erq, Typ (Pos, ty)) -> erq, ty | _ -> assert false in
     ty, Elab (erq, fun e -> None, ek e)
  | Some (bounds, flow, gen) ->
     let rq = map_free_elab_req envgc_level 0 gen rq in
     let erq, ty = match rq with Pair(erq, Typ (Pos, ty)) -> erq, ty | _ -> assert false in
     let ty = Tpoly { names = SymMap.empty; bounds; flow; body = ty } in
     let erq = Gen { pol = Pos; bounds; flow; body = erq } in
     wf_typ Pos env ty;
     wf_elab_req env erq;
     ty, Elab (erq, fun (poly, e) -> Some poly, ek e)

let elab_poly env poly (fn : env -> typ * 'a elab) : typ * (typolybounds option * 'a) elab =
  match poly with
  | None ->
     let ty, elab = fn env in
     ty, let* elab = elab in None, elab
  | Some poly ->
     let names, nbounds, pbounds, flow = poly_of_typolybounds env poly in
     let env', level', _inst = enter_poly_neg' env names nbounds flow in
     let ty, (Elab (erq, ek)) = fn env' in

     (* hack *)
     let rq = Pair (erq, Typ(Pos, ty)) in
     let rq = map_free_elab_req level' 0 (env_gen_var Esort_flexible) rq in
     let erq, ty = match rq with Pair(erq, Typ(Pos, ty)) -> erq, ty | _ -> assert false in

     let ty = Tpoly { names; bounds = pbounds; flow; body = ty } in
     (* FIXME: what's the right pol here? *)
     let erq = Gen { pol = Pos; bounds = pbounds; flow; body = erq } in
     wf_typ Pos env ty;
     wf_elab_req env erq;
     ty, Elab (erq, fun (poly, e) -> Some poly, ek e)

let rec check env e (ty : typ) : exp elab =
  wf_typ Neg env ty;
  match e with
  | None, _ -> failwith "bad exp"
  | Some e, loc ->
     let* e = check' env e ty in
     Some e, loc
and check' env e ty =
  match e, ty with
  | If (e, ifso, ifnot), _ ->
     let* e = check env e (cons_typ Neg Bool)
     and* ifso = check env ifso ty
     and* ifnot = check env ifnot ty in
     If (e, ifso, ifnot)
  | Parens e, _ ->
     let* e = check env e ty in
     Parens e
  | Tuple ef, Tcons (Record tf) ->
     let merged =
       merge_fields ef tf
         ~both:(fun _fn e ty -> Some (check env e ty))
         ~left:(fun _fn e -> ignore (infer env e); None (* FIXME: not a great elab, this! *))
         ~right:(fun fn _ty -> failwith ("missing " ^ string_of_field_name fn) )
         ~extra:(function
           | _, (`Closed, `Extra) -> failwith "extra"
           | (`Open, _), _ -> assert false (* no open tuples *)
           | (`Closed, `Extra), _ -> failwith "missing"
           | _ -> `Closed) in
     let* ef = elab_fields merged in
     Tuple ef
  | Proj (e, (field, loc)), _ ->
     (* Because of subtyping, there's a checking form for Proj! *)
     let r = { fields = FieldMap.singleton (Field_named field) ty;
               fnames = [Field_named field];
               fopen = `Open } in
     let* e = check env e (Tcons (Record r)) in
     Proj (e, (field, loc))
  | Let (p, pty, e, body), _ ->
     let pty, e = check_or_infer env pty e in
     let vs = check_pat env SymMap.empty pty p in
     let env = env_cons_entry env (Evals vs) in
     let* e, ety = e and* body = check env body ty in
     Let(p, Some ety, e, body)
  (* FIXME not good *)
(*
  | Fn _, Tpoly { names = _; bounds; flow; body } ->
     (* The names should not be in scope in the body *)
     let names = SymMap.empty in
     let env, ty = enter_poly_neg env names bounds flow body in
     check' env e ty
  | Fn (None, params, ret, body), Tcons (Func (ptypes, rtype)) ->
     (* If poly <> None, then we should infer & subtype *)
     let orig_env = env in
     let env_gen = env_cons orig_env (Eflexible {vars=Vector.create (); names=SymMap.empty}) in
     let vs = check_parameters env_gen SymMap.empty params ptypes in
     let env' = env_cons env_gen (Evals vs) in
     check env' body (check_annot env' ret rtype)
*)
  | Pragma "true", Tcons Bool -> elab_pure e
  | Pragma "false", Tcons Bool -> elab_pure e
  (* FIXME: in the Tsimple case, maybe keep an existing flex level? *)
  | e, _ ->
     (* Default case: infer and subtype. *)
     let ty', e = infer' env e in
     subtype env ty' ty |> report;
     wf_typ Neg env ty;
     let* e = e in e

and infer env : exp -> typ * exp elab = function
  | None, _ -> failwith "bad exp"
  | Some e, loc ->
     let ty, e = infer' env e in
     wf_typ Pos env ty;
     ty, (let* e = e in Some e, loc)
and infer' env : exp' -> typ * exp' elab = function
  | Lit l -> infer_lit l
  | Var (id, _loc) as e -> env_lookup_var env id, elab_pure e
  | Typed (e, ty) ->
     let tn, tp = typ_of_tyexp env ty in
     tp, let* e = check env e tn in Typed (e, ty)
  | Parens e ->
     let ty, e = infer env e in
     ty, let* e = e in Parens e
  | If (e, ifso, ifnot) ->
     let e = check env e (cons_typ Neg Bool)
     and tyso, ifso = infer env ifso
     and tynot, ifnot = infer env ifnot in
     (* FIXME: join of typ? Rank1 join? *)
     let level = flex_level env in
     Tsimple (join Pos (approx env level Pos tyso) (approx env level Pos tynot)),
     let* e = e and* ifso = ifso and* ifnot = ifnot in
     If (e, ifso, ifnot)
  | Proj (e, (field, loc)) ->
     let ty, e = infer env e in
     let res = ref (Tcons Bot) in
     let tmpl = (Record { fields = FieldMap.singleton (Field_named field) res;
                          fnames = [Field_named field]; fopen = `Open }) in
     match_type env (lazy (flex_level env)) ty tmpl |> report;
     !res, let* e = e in Proj (e, (field,loc))
  | Tuple fields ->
     let fields = map_fields (fun _fn e -> infer env e) fields in
     cons_typ Pos (Record (map_fields (fun _ (ty, _e) -> ty) fields)),
     let* fields = elab_fields (map_fields (fun _fn (_ty, e) -> e) fields) in
     Tuple fields
  | Pragma "bot" as e -> cons_typ Pos Bot, elab_pure e
  | Pragma s -> failwith ("pragma: " ^ s)
  | Let (p, pty, e, body) ->
     let pty, e = check_or_infer env pty e in
     let vs = check_pat env SymMap.empty pty p in
     let env = env_cons_entry env (Evals vs) in
     let res, body = infer env body in
     res,
     let* e, ety = e and* body = body in
     Let(p, Some ety, e, body)
  | Fn (poly, params, ret, body) ->
     let ty, elab =
       elab_poly env poly (fun env ->
         elab_gen env (fun env ->
         let params = map_fields (fun _fn (p, ty) ->
           match ty with
           | Some ty -> typ_of_tyexp env ty, p
           | None -> fresh_flow env, p) params in
         let vs = fold_fields (fun acc fn ((_tn, tp), p) ->
           match fn, p with
           | _, p -> check_pat env acc tp p) SymMap.empty params in
         let env' = env_cons_entry env (Evals vs) in
         let res, body = check_or_infer env' ret body in
         cons_typ Pos (Func (map_fields (fun _fn ((tn, _tp),_) -> tn) params, res)),
         let* params =
           elab_fields (map_fields (fun _fn ((tn, _tp), pat) ->
             elab_pair (elab_pure pat) (elab_typ Neg tn)) params)
         and* body = body in
         params, body)) in
     ty,
     let* poly_annot, (poly_inf, (params, (body, ret))) = elab in
     let poly =
       match poly_annot, poly_inf with
       | None, None -> None
       | Some p, None | None, Some p -> Some p
       | Some p, Some q ->
          (* Variable names are distinct, see type_print freshening *)
          (* FIXME: assert this *)
          Some (p @ q)
     in
     Fn (poly,
         map_fields (fun _ (p, ty) -> p, Some ty) params,
         Some ret,
         body)
  | App (f, args) ->
     let fty, f = infer env f in
     let args = map_fields (fun _fn e -> e, ref (Tcons Top)) args in
     let res = ref (Tcons Bot) in
     let argtmpl = map_fields (fun _fn (_e, r) -> r) args in
     match_type env (lazy (flex_level env)) fty (Func (argtmpl, res)) |> report;
     let args = map_fields (fun _fn (e, r) -> check env e !r) args in
     !res,
     let* f = f and* args = elab_fields args in
     App(f, args)


and check_pat_field env acc (ty : typ) fn p =
  match fn, p with
  | _, p -> check_pat env acc ty p

and check_pat env acc ty = function
  | None, _ -> failwith "bad pat"
  | Some p, _ -> check_pat' env acc ty p
and check_pat' env acc ty = function
  | Pvar (s,_) when SymMap.mem s acc -> failwith "duplicate bindings"
  | Pvar (s,_) -> SymMap.add s ty acc
  | Pparens p -> check_pat env acc ty p
  | Ptuple fs ->
     let fs = map_fields (fun _fn p -> p, ref (Tcons Bot)) fs in
     let trec : typ ref tuple_fields = map_fields (fun _fn (_p, r) -> r) fs in
     match_type env (lazy (flex_level env)) ty (Record trec) |> report;
     fold_fields (fun acc fn (p, r) ->
         check_pat_field env acc !r fn p) acc fs

and check_parameters env acc params ptypes =
  let merged =
    merge_fields params ptypes
      ~both:(fun _fn (p,aty) typ ->
        let ty =
          match aty with
          | None -> typ
          | Some ty ->
             let (tn, tp) = typ_of_tyexp env ty in
             subtype env typ tn |> report;
             tp in
        Some (p, ty))
      ~left:(fun _fn (_p, _aty) -> failwith "extra param")
      ~right:(fun _fn _typ -> failwith "missing param")
      ~extra:(fun _ -> `Closed) in
  fold_fields (fun acc _fn (p, ty) ->
    check_pat env acc ty p) acc merged

and infer_lit = function
  | l, loc -> infer_lit' l, elab_pure (Lit (l, loc))
and infer_lit' = function
  | Bool _ -> cons_typ Pos Bool
  | Int _ -> cons_typ Pos Int
  | String _ -> cons_typ Pos String

and check_or_infer env ty e : typ * (exp * tyexp) elab =
  match ty with
  | None ->
     let ty, e = infer env e in
     ty,
     let* e = e and* ty = elab_typ Pos ty in
     e, ty
  | Some ty ->
     let (tn, tp) = typ_of_tyexp env ty in
     tp,
     let* e = check env e tn
     and* ty = elab_pure ty in
     e, ty

and check_annot env annot ty =
  wf_typ Neg env ty;
  match annot with
  | None -> ty
  | Some ty' ->
     let tn, tp = typ_of_tyexp env ty' in
     subtype env tp ty |> report;
     tn
*)
