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

let close_tys (type s) (sort : s ty_sort) lvl pol (t : s) : s =
  let env_gen_var pol index vs rest =
    assert (is_trivial pol rest);
    assert (Intlist.is_singleton vs);
    let (var, ()) = Intlist.as_singleton vs in
    Bound_var { pol; index; var } in
  match sort with
  | Simple ->
     map_free_styp lvl 0 env_gen_var pol t
  | Gen ->
     map_free_typ lvl 0 env_gen_var pol t

(* FIXME: don't always enter Erigid during parsing! *)

let rec env_lookup_type : type s . s ty_sort -> env -> string -> s * s =
  fun sort env name ->
  match env.entry with
  | (Erigid { names; _ } | Eflexible { names; _ })
       when SymMap.mem name names ->
     (* FIXME shifting? *)
     let i = SymMap.find name names in
     (tys_of_styp sort (styp_var Neg env.level i),
      tys_of_styp sort (styp_var Pos env.level i))
  | _ ->
     match env.rest with
     | Some env -> env_lookup_type sort env name
     | None ->
        match name with
        | "any" ->
           tys_cons sort Neg Top, tys_cons sort Pos Top
        | "nothing" ->
           tys_cons sort Neg Bot, tys_cons sort Pos Bot
        | "bool" ->
           tys_cons sort Neg Bool, tys_cons sort Pos Bool
        | "int" ->
           tys_cons sort Neg Int, tys_cons sort Pos Int
        | "string" ->
           tys_cons sort Neg String, tys_cons sort Pos String
        | _ -> failwith ("unknown type " ^ name)

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
     let env, _ = enter_poly_neg env names nbounds flow (Tcons (ident Neg)) in
     let bn, bp = typ_of_tyexp sort env body in
     let bn = close_tys Gen env.level Neg bn in
     let bp = close_tys Gen env.level Pos bp in
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
  let env = env_cons env (Erigid {
    names = var_ix;
    vars = bounds |> Vector.to_array |> Array.map (fun (name,_) ->
      { name = Some name;
        rig_lower = styp_trivial Neg;
        rig_upper = styp_trivial Pos });
    flow = Flow_graph.empty (Vector.length bounds);
  }) in
  let bound_of_tyexp (ty : tyexp) =
    let n, p = typ_of_tyexp Simple env ty in
    close_tys Simple env.level Neg n,
    close_tys Simple env.level Pos p in
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
               let upper = Some (bound_of_tyexp bound) in
               lower, upper, flow
            | `Sup, None, _ ->
               let lower = Some (bound_of_tyexp bound) in
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
  match env.entry with
  | Evals vs when SymMap.mem v.label vs ->
     if v.shift = 0 then SymMap.find v.label vs else
       env_lookup_var_rest env { v with shift = v.shift - 1 }
  | _ -> env_lookup_var_rest env v
and env_lookup_var_rest env v =
  match env.rest with
  | None -> failwith (v.label ^ " not in scope")
  | Some env -> env_lookup_var env v


let report errs = List.iter (function
   | Incompatible -> failwith "incompat"
   | Missing k -> failwith ("missing " ^ string_of_field_name k)
   | Extra _ -> failwith ("extra")) errs

let rec flex_level env =
  match env.entry with
  | Eflexible _ -> env.level
  | _ ->
     match env.rest with
     | None -> failwith "nowhere to put a flex var"
     | Some env -> flex_level env

let fresh_flow env =
  let p, n = fresh_flow env (flex_level env) in
  Tsimple p, Tsimple n

let rec check env e (ty : typ) =
  wf_typ Neg env ty;
  match e with
  | None, _ -> failwith "bad exp"
  | Some e, _ -> check' env e ty
and check' env e ty =
  match e, ty with
  | If (e, ifso, ifnot), _ ->
     check env e (cons_typ Neg Bool);
     check env ifso ty;
     check env ifnot ty
  | Parens e, _ ->
     check env e ty
  | Tuple ef, Tcons (Record tf) ->
     subtype_cons_fields Pos ef tf (fun _pol _fn e ty ->
       check env e ty; []
     ) |> report
  | Proj (e, (field, _loc)), _ ->
     (* Because of subtyping, there's a checking form for Proj! *)
     let r = { fields = FieldMap.singleton (Field_named field) ty;
               fnames = [Field_named field];
               fopen = `Open } in
     check env e (Tcons (Record r))
  | Let (p, pty, e, body), _ ->
     let pty = check_or_infer env pty e in
     let vs = check_pat env SymMap.empty pty p in
     let env = env_cons env (Evals vs) in
     check env body ty
  (* FIXME not good *)
  | Fn _, Tpoly { names = _; bounds; flow; body } ->
     (* The names should not be in scope in the body *)
     let names = SymMap.empty in
     let env, ty = enter_poly_neg env names bounds flow body in
     check' env e ty
  | Fn (None, params, ret, body), Tcons (Func (ptypes, rtype)) ->
     (* If poly <> None, then we should infer & subtype *)
     let orig_env = env in
     let env_gen = env_cons orig_env (Eflexible {vars=Vector.create (); names=SymMap.empty}) in
     let vs = check_parameters env_gen SymMap.empty ptypes params in
     let env' = env_cons env_gen (Evals vs) in
     check env' body (check_annot env' ret rtype)
  | Pragma "true", Tcons Bool -> ()
  | Pragma "false", Tcons Bool -> ()
  (* FIXME: in the Tsimple case, maybe keep an existing level? *)
  | e, _ ->
     (* Default case: infer and subtype. *)
     let ty' = infer' env e in
     subtype env ty' ty |> report;
     wf_typ Neg env ty

and infer env = function
  | None, _ -> failwith "bad exp"
  | Some e, _ -> let ty = infer' env e in wf_typ Pos env ty; ty
and infer' env = function
  | Lit l -> infer_lit l
  | Var (id, _loc) -> env_lookup_var env id
  | Typed (e, ty) ->
     let tn, tp = typ_of_tyexp env ty in
     check env e tn; tp
  | Parens e -> infer env e
  | If (e, ifso, ifnot) ->
     check env e (cons_typ Neg Bool);
     let tyso = infer env ifso and tynot = infer env ifnot in
     (* FIXME: join of typ? Rank1 join? *)
     Tsimple (join Pos (approx env env.level Pos tyso) (approx env env.level Pos tynot))
  | Proj (e, (field,_loc)) ->
     let ty = infer env e in
     let res = ref (Tcons Bot) in
     let tmpl = (Record { fields = FieldMap.singleton (Field_named field) res;
                          fnames = [Field_named field]; fopen = `Open }) in
     match_type env (lazy (flex_level env)) ty tmpl |> report;
     !res
  | Tuple fields ->
     let fields = map_fields (fun _fn e -> infer env e) fields in
     cons_typ Pos (Record fields)
  | Pragma "bot" -> cons_typ Pos Bot
  | Pragma s -> failwith ("pragma: " ^ s)
  | Let (p, pty, e, body) ->
     let pty = check_or_infer env pty e in
     let vs = check_pat env SymMap.empty pty p in
     let env = env_cons env (Evals vs) in
     infer env body
  | Fn (poly, params, ret, body) ->
     let orig_env = env in
     let poly = Option.map (poly_of_typolybounds env) poly in
     let poly_env =
       match poly with
       | None -> orig_env
       | Some (names, nbounds, _pbounds, flow) ->
          fst (enter_poly_neg env names nbounds flow (Tcons (ident Neg))) in
     let env = env_cons poly_env (Eflexible {vars=Vector.create ();names=SymMap.empty}) in
     let params = map_fields (fun _fn (p, ty) ->
       match ty with
       | Some ty -> typ_of_tyexp env ty, p
       | None -> fresh_flow env, p) params in
     let vs = fold_fields (fun acc fn ((_tn, tp), p) ->
       match fn, p with
       | _, p -> check_pat env acc tp p) SymMap.empty params in
     let env' = env_cons env (Evals vs) in
     let res = check_or_infer env' ret body in
     let ty = cons_typ Pos (Func (map_fields (fun _fn ((tn,_tp),_p) -> tn) params, res)) in
     wf_typ Pos env ty; (* no dependency for now! Probably never, inferred. *)
(*     let ty = Type_simplification.canonise env ty in*)
     let ty = Type_simplification.remove_joins env env.level ty in
     let envgc, ty = Type_simplification.garbage_collect env env.level ty in
     wf_typ Pos envgc ty;
     let ty = generalise envgc envgc.level ty in
     wf_typ Pos poly_env ty;
     let ty = mark_principal Pos ty in
     wf_typ Pos poly_env ty;
     let ty =
       match poly with
       | None -> ty
       | Some (names, _nbounds, pbounds, flow) ->
          let ty = close_tys Gen poly_env.level Pos ty in
          Tpoly {names; bounds=pbounds; flow; body=ty} in
     wf_typ Pos orig_env ty;
     ty
  | App (f, args) ->
     let fty = infer env f in
     let args = map_fields (fun _fn e -> e, ref (Tcons Top)) args in
     let res = ref (Tcons Bot) in
     let argtmpl = map_fields (fun _fn (_e, r) -> r) args in
     match_type env (lazy (flex_level env)) fty (Func (argtmpl, res)) |> report;
     fold_fields (fun () _fn (e, r) -> check env e !r) () args;
     !res


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

and check_parameters env acc ptypes fs =
  (* FIXME: I think this also just needs subtype_cons_fields to fold? *)
  let fs = map_fields (fun _fn (p,ty) -> p, ty, ref None) fs in
  subtype_cons_fields Pos ptypes fs (fun pol _fn p (_pat, ty, r) ->
    assert (!r = None); assert (pol = Pos);
    wf_typ pol env p;
    let ty =
      match ty with
      | None -> p
      | Some ty ->
         let (tn, tp) = typ_of_tyexp env ty in
         subtype env p tn |> report;
         tp in
    r := Some ty;
    []) |> report;
  fold_fields (fun acc _fn (p, _ty, r) ->
    let ty = match !r with Some r -> r | None -> failwith "check_pat match?" in
    check_pat env acc ty p) acc fs

and infer_lit = function
  | l, _ -> infer_lit' l
and infer_lit' = function
  | Bool _ -> cons_typ Pos Bool
  | Int _ -> cons_typ Pos Int
  | String _ -> cons_typ Pos String

and check_or_infer env ty e =
  match ty with
  | None ->
     infer env e
  | Some ty ->
     let (tn, tp) = typ_of_tyexp env ty in
     check env e tn;
     tp

and check_annot env annot ty =
  wf_typ Neg env ty;
  match annot with
  | None -> ty
  | Some ty' ->
     let tn, tp = typ_of_tyexp env ty' in
     subtype env tp ty |> report;
     tn
