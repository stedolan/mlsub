open Tuple_fields
open Exp
open Typedefs
open Types

let unimp () = failwith "unimplemented"

type _ ty_sort =
  | Simple : styp ty_sort
  | Gen : typ ty_sort
let tys_cons (type a) (sort : a ty_sort) pol (x : a cons_head) : a =
  match sort with
  | Simple -> styp_cons pol x
  | Gen -> cons_typ pol x
let tys_of_styp (type a) (sort : a ty_sort) (x : styp) : a =
  match sort with
  | Simple -> x
  | Gen -> Tsimple x

let env_gen_var sort pol index vs rest =
  assert (is_trivial pol rest);
  assert (Intlist.is_singleton vs);
  let (var, ()) = Intlist.as_singleton vs in
  styp_bvar pol sort index var

let close_tys (type s) (sort : s ty_sort) lvl vsort pol (t : s) : s =
  match sort with
  | Simple ->
     map_free_styp lvl 0 (env_gen_var vsort) pol t
  | Gen ->
     map_free_typ lvl 0 (env_gen_var vsort) pol t

(* FIXME: don't always enter Erigid during parsing! *)

let env_lookup_type sort env name =
  match env_lookup_type_var env name with
  | Some (n, p) -> (tys_of_styp sort n, tys_of_styp sort p)
  | None ->
     match lookup_named_type name with
     | Some cons -> tys_cons sort Neg cons, tys_cons sort Pos cons
     | None ->
        failwith ("unknown type " ^ name)

(* Returns a A⁻ ≤ A⁺ pair *)
let rec typ_of_tyexp : type s . s ty_sort -> env -> tyexp -> s * s  =
  fun sort env ty -> match ty with
  | None, _ -> failwith "bad type"
  | Some t, _ -> typ_of_tyexp' sort env t
and typ_of_tyexp' : type s . s ty_sort -> env -> tyexp' -> s * s =
  fun sort env tyexp -> match tyexp with
  | Tnamed (name, _) ->
     env_lookup_type sort env name.label
  | Trecord fields ->
     let ns, ps = typs_of_tuple_tyexp sort env fields in
     tys_cons sort Neg (Record ns), tys_cons sort Pos (Record ps)
  | Tfunc (args, res) ->
     let ans, aps = typs_of_tuple_tyexp sort env args in
     let rn, rp = typ_of_tyexp sort env res in
     tys_cons sort Neg (Func (aps, rn)), tys_cons sort Pos (Func (ans, rp))
  | Tparen t ->
     typ_of_tyexp sort env t
  | Tjoin _ | Tmeet _ -> unimp ()
  | Tforall (vars, body) ->
     let () =
       match body with Some (Tfunc _),_ ->  () | _ -> failwith "expected a function type" in
     match sort with Simple -> failwith "simple type expected" | Gen ->
     let names, nbounds, pbounds, flow = poly_of_typolybounds env vars in
     (* FIXME: slightly horrible to use a Neg context here.
        Possible fixes: have a just-names envsort, or have two envs *)
     let env, level, _ = enter_poly_neg env names nbounds flow (Tcons (ident Neg)) in
     let bn, bp = typ_of_tyexp sort env body in
     let bn = close_tys Gen level Esort_rigid Neg bn in
     let bp = close_tys Gen level Esort_flexible Pos bp in
     Tpoly {names; bounds=nbounds; flow; body=bn},
     Tpoly {names; bounds=pbounds; flow; body=bp}

and typs_of_tuple_tyexp : type s . s ty_sort -> env -> tyexp tuple_fields -> s tuple_fields * s tuple_fields =
  fun sort env t ->
  let t = map_fields (fun _fn t -> typ_of_tyexp sort env t) t in
  map_fields (fun _fn (tn, _tp) -> tn) t,
  map_fields (fun _fn (_tn, tp) -> tp) t

(* FIXME crazy type *)
and poly_of_typolybounds env (vars : typolybounds) :
  int SymMap.t *
    (string option * styp * styp) array * (string option * styp * styp) array * Flow_graph.t =
  let bounds = Vector.create () in
  let var_ix =
    List.fold_left (fun m ((v,_), bound) ->
      match SymMap.find v m with
      | i ->
         Vector.push (snd (Vector.get bounds i)) bound |> ignore; m
      | exception Not_found ->
         let bv = Vector.create () in
         ignore (Vector.push bv bound);
         SymMap.add v (Vector.push bounds (v,bv)) m) SymMap.empty vars in
  let rec check_flow = function None, _ -> failwith "bad type" | Some t, _ ->
    match t with
    | Tnamed ({label;_}, _) when SymMap.mem label var_ix -> Some (SymMap.find label var_ix)
    | Tnamed _ | Trecord _ | Tfunc _ -> None
    | Tparen t -> check_flow t
    | Tjoin _ | Tmeet _ -> unimp ()
    | Tforall _ -> failwith "expected styp" in
  let nvars = Vector.length bounds in
  let level = env_next_level env Esort_rigid in
  let env = env_cons env level (Erigid {
    names = var_ix;
    vars = bounds |> Vector.to_array |> Array.map (fun (name,_) ->
      { name = Some name;
        rig_lower = styp_trivial Neg;
        rig_upper = styp_trivial Pos });
    flow = Flow_graph.empty (Vector.length bounds);
  }) in
  let bound_of_tyexp nsort psort (ty : tyexp) =
    let n, p = typ_of_tyexp Simple env ty in
    close_tys Simple level nsort Neg n,
    close_tys Simple level psort Pos p in
  let bounds = Vector.to_array bounds |> Array.mapi (fun i (name,bounds) ->
    let lower, upper, flow =
      Vector.fold_lefti (fun (lower, upper, flow) _ bound ->
      match bound with
      | None -> lower, upper, flow
      | Some (dir, bound) ->
         match check_flow bound with
         | Some j ->
            let edge = match dir with `Sub -> (i, j) | `Sup -> (j, i) in
            lower, upper, edge :: flow
         | None ->
            match dir, lower, upper with
            | `Sub, _, Some _ -> failwith "duplicate upper bounds"
            | `Sup, Some _, _ -> failwith "duplicate lower bounds"
            | `Sub, _, None ->
               let upper = Some (bound_of_tyexp Esort_flexible Esort_rigid bound) in
               lower, upper, flow
            | `Sup, None, _ ->
               let lower = Some (bound_of_tyexp Esort_rigid Esort_flexible bound) in
               lower, upper, flow
      ) (None, None, []) bounds in
    (Some name, lower, upper, flow)) in
  let flow = bounds |> Array.map (fun (_,_,_,f) -> f) |> Array.to_list |> List.concat |> Flow_graph.of_list nvars in
  let bounds = bounds |> Array.map (fun (name,l,u,_) ->
    let ln, lp = match l with
      | None -> (styp_bot Neg, styp_bot Pos)
      | Some l -> l in
    let un, up = match u with
      | None -> (styp_top Neg, styp_top Pos)
      | Some u -> u in
    (name, ln, up), (name, lp, un)) in
  var_ix, Array.map fst bounds, Array.map snd bounds, flow

  


let typ_of_tyexp env t =
  let (tn, tp) = typ_of_tyexp Gen env t in
  wf_typ Neg env tn; wf_typ Pos env tp;
  (tn, tp)

let rec env_lookup_var env v =
  match env with
  | Env_nil -> failwith (v.label ^ " not in scope")
  | Env_cons { entry = Evals vs; rest; _ }
       when SymMap.mem v.label vs ->
     if v.shift = 0 then SymMap.find v.label vs else
       env_lookup_var rest { v with shift = v.shift - 1 }
  | Env_cons { rest; _ } ->
     env_lookup_var rest v

let report errs = List.iter (function
   | Incompatible -> failwith "incompat"
   | Missing k -> failwith ("missing " ^ string_of_field_name k)
   | Extra _ -> failwith ("extra")) errs

let rec flex_level env =
  match env with
  | Env_cons { entry = Eflexible _; level; _ } -> level
  | Env_cons { rest; _ } -> flex_level rest
  | _ -> failwith "nowhere to put a flex var"

let fresh_flow env =
  let p, n = fresh_flow env (flex_level env) in
  Tsimple p, Tsimple n


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
