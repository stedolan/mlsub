open Tuple_fields
open Exp
open Typedefs
open Types

let report = function
(* FIXME enable & promote tests *)
  (* | Incompatible (s,t) -> failwith (Printf.sprintf "incompat %s <: %s" s t) *)
  | Incompatible _ -> failwith "incompat"
  | Missing k -> failwith ("missing " ^ string_of_field_name k)
  | Extra _ -> failwith ("extra")


let rec env_lookup_var env v =
  match env with
  | Env_nil -> failwith (v.label ^ " not in scope")
  | Env_vals { vals = vs; rest; _ }
       when SymMap.mem v.label vs ->
     if v.shift = 0 then SymMap.find v.label vs else
       env_lookup_var rest { v with shift = v.shift - 1 }
  | Env_types { rest; _ } | Env_vals {rest; _}->
     env_lookup_var rest v

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


open Elab

let elab_gen (env:env) (fn : env -> ptyp * 'a elab) : ptyp * (typolybounds option * 'a) elab =
  let level = Env_level.extend (env_level env) in
  let env' = Env_types { level; rig_names = SymMap.empty; rig_defns = IArray.empty; rest = env } in
  let ty, Elab (erq, ek) = fn env' in
  wf_ptyp env' ty;

  let rec fixpoint visit erq ty =
    if visit > 10 then intfail "looping?";
    let changes = ref [] in
    let ty = expand_ptyp visit ~changes env' level ty in
    let erq = elabreq_map_typs erq ~index:0
                ~neg:(fun ~index:_ -> expand_ntyp visit ~changes env' level)
                ~pos:(fun ~index:_ -> expand_ptyp visit ~changes env' level) in
    if !changes <> [] then
      fixpoint (visit+2) erq ty
    else
      (visit, erq, ty) in
  let visit, erq, ty = fixpoint 2 erq ty in

  let bvars = Vector.create () in
  let ty = substn_ptyp visit bvars level ~index:0 ty in
  let erq = elabreq_map_typs erq ~index:0
              ~neg:(substn_ntyp visit bvars level)
              ~pos:(substn_ptyp visit bvars level) in
  if Vector.length bvars = 0 then
    ty, Elab (erq, fun e -> None, ek e)
  else
    let next_name = ref 0 in
    let rec mkname () =
      let n = !next_name in
      incr next_name;
      let name = match n with
        | n when n < 26 -> Printf.sprintf "%c" (Char.chr (Char.code 'A' + n))
        | n -> Printf.sprintf "T_%d" (n-26) in
      match env_lookup_type_var env name with
      | None -> name
      | Some _ -> mkname () in
    let bounds = bvars |> Vector.to_array |> Array.map (fun (_,r) -> mkname (), !r) |> IArray.of_array in
    let ty = Tpoly { vars = bounds; body = ty } in
    ty, Elab (Gen{bounds; body=erq}, fun (poly, e) -> Some poly, ek e)
  
(*
  let level' = env_next_level env Esort_flexible in
  let env' = env_cons env level' (Eflexible {vars=Vector.create(); names=SymMap.empty}) in
  let ty, (Elab (erq, ek)) = fn env' in
  wf_ptyp env' ty;
  (* FIXME hack *)
  let rq = Pair(erq, Ptyp ty) in
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
*)

let fresh_flow env =
  let fv = fresh_flexvar (env_level env) in
  Tvar (Vflex fv)


(*
let elab_poly env poly (fn : env -> ptyp * 'a elab) : ptyp * (typolybounds option * 'a) elab =
  match poly with
  | None ->
     let ty, elab = fn env in
     ty, let* elab = elab in None, elab
  | Some poly ->
     let names, nbounds, pbounds, flow = poly_of_typolybounds env poly in
     let env', level', _inst = enter_poly_neg' env names nbounds flow in
     let ty, (Elab (erq, ek)) = fn env' in

     (* hack *)
     let rq = Pair (erq, Ptyp ty) in
     let rq = map_free_elab_req level' 0 (env_gen_var Esort_flexible) rq in
     let erq, ty = match rq with Pair(erq, Ptyp ty) -> erq, ty | _ -> assert false in

     let ty = Tpoly { names; bounds = pbounds; flow; body = ty } in
     (* FIXME: what's the right pol here? *)
     let erq = Gen { pol = Pos; bounds = pbounds; flow; body = erq } in
     wf_ptyp env ty;
     wf_elab_req env erq;
     ty, Elab (erq, fun (poly, e) -> Some poly, ek e)
*)

let rec check env e (ty : ntyp) : exp elab =
  wf_ntyp env ty;
  match e with
  | None, _ -> failwith "bad exp"
  | Some e, loc ->
     let* e = check' env e ty in
     Some e, loc
and check' env e ty =
  match e, ty with
  | If (e, ifso, ifnot), _ ->
     let* e = check env e (Tcons Bool)
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
     let env = Env_vals { vals = vs; rest = env } in
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
     subtype ~error:report env ty' ty;
     wf_ntyp env ty;
     let* e = e in e

and infer env : exp -> ptyp * exp elab = function
  | None, _ -> failwith "bad exp"
  | Some e, loc ->
     let ty, e = infer' env e in
     wf_ptyp env ty;
     ty, (let* e = e in Some e, loc)
and infer' env : exp' -> ptyp * exp' elab = function
  | Lit l -> infer_lit l
  | Var (id, _loc) as e -> env_lookup_var env id, elab_pure e
  | Typed (e, ty) ->
     let t = typ_of_tyexp env ty in
     t, let* e = check env e t in Typed (e, ty)
  | Parens e ->
     let ty, e = infer env e in
     ty, let* e = e in Parens e
  | If (e, ifso, ifnot) ->
     let e = check env e (Tcons Bool)
     and tyso, ifso = infer env ifso
     and tynot, ifnot = infer env ifnot in
     join_ptyp env tyso tynot,
     let* e = e and* ifso = ifso and* ifnot = ifnot in
     If (e, ifso, ifnot)
  | Proj (e, (field, loc)) ->
     let ty, e = infer env e in
     let resp, res = Ivar.make () in
     let tmpl = (Record { fields = FieldMap.singleton (Field_named field) resp;
                          fnames = [Field_named field]; fopen = `Open }) in
     match_typ ~error:report env (env_level env) ty tmpl;
     Ivar.get res, let* e = e in Proj (e, (field,loc))
  | Tuple fields ->
     let fields = map_fields (fun _fn e -> infer env e) fields in
     Tcons (Record (map_fields (fun _ (ty, _e) -> ty) fields)),
     let* fields = elab_fields (map_fields (fun _fn (_ty, e) -> e) fields) in
     Tuple fields
  | Pragma "bot" as e -> Tcons Bot, elab_pure e
  | Pragma s -> failwith ("pragma: " ^ s)
  | Let (p, pty, e, body) ->
     let pty, e = check_or_infer env pty e in
     let vals = check_pat env SymMap.empty pty p in
     let env = Env_vals { rest=env; vals } in
     let res, body = infer env body in
     res,
     let* e, ety = e and* body = body in
     Let(p, Some ety, e, body)
  | Fn (poly, params, ret, body) ->
     let ty, elab =
ignore poly;((*FIXME       elab_poly env poly (fun env ->*)
         elab_gen env (fun env ->
         let params = map_fields (fun _fn (p, ty) ->
           match ty with
           | Some ty -> typ_of_tyexp env ty, p
           | None -> fresh_flow env, p) params in
         let vs = fold_fields (fun acc fn (t, p) ->
           match fn, p with
           | _, p -> check_pat env acc t p) SymMap.empty params in
         let env' = Env_vals { vals = vs; rest = env } in
         let res, body = check_or_infer env' ret body in
         let _ = map_fields (fun _fn (t,_) -> wf_ntyp env t) params in
         Tcons (Func (map_fields (fun _fn (t,_) -> t) params, res)),
         let* params =
           elab_fields (map_fields (fun _fn (t, pat) ->
             elab_pair (elab_pure pat) (elab_ntyp t)) params)
         and* body = body in
         params, body)) in
     ty,
     let* (*poly_annot, *) (poly_inf, (params, (body, ret))) = elab in
     let poly =
       match (*poly_annot,*) None, poly_inf with
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
     let args = map_fields (fun _fn e -> e, Ivar.make ()) args in
     let resp, res = Ivar.make () in
     let argtmpl = map_fields (fun _fn (_e, (r, _)) -> r) args in
     wf_ptyp env fty;
     match_typ ~error:report env (env_level env) fty (Func (argtmpl, resp));
     wf_ptyp env fty;
     let args = map_fields (fun _fn (e, (_,r)) -> check env e (Ivar.get r)) args in
     Ivar.get res,
     let* f = f and* args = elab_fields args in
     App(f, args)


and check_pat_field env acc (ty : ptyp) fn p =
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
     let fs = map_fields (fun _fn p -> p, Ivar.make ()) fs in
     let trec : _ tuple_fields = map_fields (fun _fn (_p, (r,_)) -> r) fs in
     match_typ ~error:report env (env_level env) ty (Record trec);
     fold_fields (fun acc fn (p, (_,r)) ->
         check_pat_field env acc (Ivar.get r) fn p) acc fs

and check_parameters env acc params ptypes =
  let merged =
    merge_fields params ptypes
      ~both:(fun _fn (p,aty) typ ->
        let ty =
          match aty with
          | None -> typ
          | Some ty ->
             let t = typ_of_tyexp env ty in
             subtype ~error:report env typ t;
             t in
        Some (p, ty))
      ~left:(fun _fn (_p, _aty) -> failwith "extra param")
      ~right:(fun _fn _typ -> failwith "missing param")
      ~extra:(fun _ -> `Closed) in
  fold_fields (fun acc _fn (p, ty) ->
    check_pat env acc ty p) acc merged

and infer_lit = function
  | l, loc -> infer_lit' l, elab_pure (Lit (l, loc))
and infer_lit' = function
  | Bool _ -> Tcons Bool
  | Int _ -> Tcons Int
  | String _ -> Tcons String

and check_or_infer env ty e : ptyp * (exp * tyexp) elab =
  match ty with
  | None ->
     let ty, e = infer env e in
     ty,
     let* e = e and* ty = elab_ptyp ty in
     e, ty
  | Some ty ->
     let t = typ_of_tyexp env ty in
     t,
     let* e = check env e t
     and* ty = elab_pure ty in
     e, ty

and check_annot env annot ty =
  wf_ntyp env ty;
  match annot with
  | None -> ty
  | Some ty' ->
     let t = typ_of_tyexp env ty' in
     subtype ~error:report env t ty;
     t
