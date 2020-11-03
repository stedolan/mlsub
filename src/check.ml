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
  | Simple -> cons_styp pol vsnil x
  | Gen -> cons_typ pol x
let tys_of_styp (type a) (sort : a ty_sort) (x : styp) : a =
  match sort with
  | Simple -> x
  | Gen -> Tsimple x

type env_ext =
  | Env of env
  | Ext of { level : Env_level.t; mark : Env_marker.t; vars: int SymMap.t; rest : env_ext }

let env_extend env vars =
  let level = match env with Env { level; _ } | Ext { level; _ } -> level in
  let level = Env_level.extend level in
  let mark = Env_marker.make () in
  Ext { level; mark; vars; rest = env }, level, mark

let env_gen_var pol index (_mark', vs) rest =
  assert (Type_simplification.is_trivial pol rest);
  assert (Intlist.is_singleton vs);
  let (var, ()) = Intlist.as_singleton vs in
  { pol; body = Bound_var { index; var } }

let rec lookup_type_var env name =
  match env with
  | Env _ -> None
  | Ext { level; mark; vars; rest } when SymMap.mem name.label vars ->
     if name.shift > 0 then lookup_type_var rest { name with shift = name.shift - 1 }
     else
       let vs = Intlist.singleton (SymMap.find name.label vars) () in
       Some (cons_styp Neg (Intlist.singleton level (mark, vs)) (ident Neg),
             cons_styp Pos (Intlist.singleton level (mark, vs)) (ident Pos))
  | Ext { rest; _ } -> lookup_type_var rest name


(* Returns a A⁻ ≤ A⁺ pair *)
let rec typ_of_tyexp : type s . s ty_sort -> env_ext -> tyexp -> s * s  =
  fun sort env ty -> match ty with
  | None, _ -> failwith "bad type"
  | Some t, _ -> typ_of_tyexp' sort env t
and typ_of_tyexp' : type s . s ty_sort -> env_ext -> tyexp' -> s * s =
  fun sort env tyexp -> match tyexp with
  | Tnamed (name, _) ->
     begin match lookup_type_var env name with
     | Some (n, p) -> (tys_of_styp sort n, tys_of_styp sort p)
     | None ->
        match name.label with
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
        | s -> failwith ("unknown type " ^ s)
     end
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
     match sort with Simple -> failwith "simple type expected" | Gen ->
     let bounds = Vector.create () in
     let var_ix =
       List.fold_left (fun m ((v,_), bound) ->
         match SymMap.find v m with
         | i ->
            Vector.push (Vector.get bounds i) bound |> ignore; m
         | exception Not_found ->
            let bv = Vector.create () in
            ignore (Vector.push bv bound);
            SymMap.add v (Vector.push bounds bv) m) SymMap.empty vars in
     let rec check_flow = function None, _ -> failwith "bad type" | Some t, _ ->
       match t with
       | Tnamed ({label;_}, _) when SymMap.mem label var_ix -> Some (SymMap.find label var_ix)
       | Tnamed _ | Trecord _ | Tfunc _ -> None
       | Tparen t -> check_flow t
       | Tjoin _ | Tmeet _ -> unimp ()
       | Tforall _ -> failwith "expected styp" in
     let nvars = Vector.length bounds in
     let env, lvl, mark = env_extend env var_ix in
     let gen_typ_of_tyexp (type s) (sort : s ty_sort) (ty : tyexp) : s * s =
       let tn, tp = typ_of_tyexp sort env ty in
       match sort with
       | Simple ->
          map_free_styp lvl mark 0 env_gen_var Neg tn,
          map_free_styp lvl mark 0 env_gen_var Pos tp
       | Gen ->
          map_free_typ lvl mark 0 env_gen_var Neg tn,
          map_free_typ lvl mark 0 env_gen_var Pos tp in
     let bounds = Vector.to_array bounds |> Array.mapi (fun i bounds ->
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
                  let upper = Some (gen_typ_of_tyexp Simple bound) in
                  lower, upper, flow
               | `Sup, None, _ ->
                  let lower = Some (gen_typ_of_tyexp Simple bound) in
                  lower, upper, flow
       ) (None, None, []) bounds) in
     let flow = bounds |> Array.map (fun (_,_,f) -> f) |> Array.to_list |> List.concat |> Flow_graph.of_list nvars in
     let bn, bp = gen_typ_of_tyexp Gen body in
     let bounds = bounds |> Array.map (fun (l,u,_) ->
       let ln, lp = match l with
         | None -> (cons_styp Neg vsnil Bot, cons_styp Pos vsnil Bot)
         | Some l -> l in
       let un, up = match u with
         | None -> (cons_styp Neg vsnil Top, cons_styp Pos vsnil Top)
         | Some u -> u in
       (ln, up), (lp, un)) in
     Tpoly (Array.map fst bounds, flow, bn),
     Tpoly (Array.map snd bounds, flow, bp)

and typs_of_tuple_tyexp : type s . s ty_sort -> env_ext -> tyexp tuple_fields -> s tuple_fields * s tuple_fields =
  fun sort env t ->
  let t = map_fields (fun _fn t -> typ_of_tyexp sort env t) t in
  map_fields (fun _fn (tn, _tp) -> tn) t,
  map_fields (fun _fn (_tn, tp) -> tp) t

let typ_of_tyexp env t =
  let (tn, tp) = typ_of_tyexp Gen (Env env) t in
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
   | Missing (`Named k) -> failwith ("missing " ^ k)
   | Missing `Positional -> failwith ("missing pos")
   | Extra _ -> failwith ("extra")) errs

(* When checking a term against a template type,
   I think it's principal to inspect a Tm_typ as long as we don't
   inspect any styps. (???)  *)
(* FIXME FIXME principality / boxiness ??? *)
let inspect = function
  | Tcons cons ->
     Tcons cons
  | t -> t

let fresh_flow env flex =
  let p, n = fresh_flow env flex in
  Tsimple p, Tsimple n

let rec check env e (ty : typ) =
  wf_typ Neg env ty;
  match e with
  | None, _ -> failwith "bad exp"
  | Some e, _ -> check' env e ty
and check' env e ty =
  match e, inspect ty with
  | If (e, ifso, ifnot), _ ->
     check env e (cons_typ Neg Bool);
     check env ifso ty;
     check env ifnot ty
  | Parens e, _ ->
     check env e ty
  | Tuple fields, Tcons (Record tf) ->
     check_fields env fields tf
  | Proj (e, (field, _loc)), _ ->
     (* Because of subtyping, there's a checking form for Proj! *)
     let r = { fpos = [];
               fnamed = SymMap.singleton field ty;
               fnames = [field];
               fopen = `Open } in
     check env e (Tcons (Record r))
  | Let (ps, es, body), _ ->
     let env = env_cons env (Eflexible (Vector.create ())) in
     let flex = (env.level, env.marker) in
     let vs = bind env flex SymMap.empty ps es in
     let env = env_cons env (Evals vs) in
     check env body ty
  | Fn (params, ret, body), Tcons (Func (ptypes, rtype)) ->
     let vs = check_pat_typed_fields env SymMap.empty ptypes params in
     let env' = env_cons env (Evals vs) in
     check env' body (check_annot env' ret rtype)
  | Pragma "true", Tcons Bool -> ()
  | Pragma "false", Tcons Bool -> ()
  (* FIXME: in the Tsimple case, maybe keep an existing flex level? *)
  | e, _ ->
     (* Default case: infer and subtype.
        Using the icfp19 rule! *)
     let env' = env_cons env (Eflexible (Vector.create ())) in
     let flex = (env'.level, env'.marker) in
     let ty' = infer' env' flex e in
     subtype env ty' ty |> report;
     wf_typ Neg env ty

and check_fields env ef tf =
  subtype_cons_fields Pos ef tf (fun _pol _fn (e, ety) ty ->
    let ty = check_annot env ety ty in
    match e with
    | Some e -> check env e ty; []
    (* FIXME punning *)
    | None -> failwith "punning unimplemented"
    ) |> report

and infer env flex = function
  | None, _ -> failwith "bad exp"
  | Some e, _ -> let ty = infer' env flex e in wf_typ Pos env ty; ty
and infer' env flex = function
  | Lit l -> infer_lit l
  | Var (id, _loc) -> env_lookup_var env id
  | Typed (e, ty) ->
     let tn, tp = typ_of_tyexp env ty in
     check env e tn; tp
  | Parens e -> infer env flex e
  | If (e, ifso, ifnot) ->
     check env e (cons_typ Neg Bool);
     let tyso = infer env flex ifso and tynot = infer env flex ifnot in
     (* FIXME: join of typ? Rank1 join? *)
     Tsimple (join Pos (approx env env.level env.marker Pos tyso) (approx env env.level env.marker Pos tynot))
  | Proj (e, (field,_loc)) ->
     let ty = infer env flex e in
     let res = ref (Tcons Bot) in
     let tmpl = (Record { fpos = [];
                          fnamed = SymMap.singleton field res;
                          fnames = [field]; fopen = `Open }) in
     match_type env flex ty tmpl |> report;
     !res
  | Tuple fields ->
     cons_typ Pos (Record (infer_fields env flex fields))
  | Pragma "bot" -> cons_typ Pos Bot
  | Pragma s -> failwith ("pragma: " ^ s)
  | Let (ps, es, body) ->
     let vs = bind env flex SymMap.empty ps es in
     let env = env_cons env (Evals vs) in
     infer env flex body
  | Fn (params, ret, body) ->
     let orig_env = env in
     let env = env_cons orig_env (Eflexible (Vector.create ())) in
     let flex = (env.level, env.marker) in
     let params = map_fields (fun _fn (p, ty) ->
       match ty with
       | Some ty -> typ_of_tyexp env ty, p
       | None -> fresh_flow env flex, p) params in
     let vs = fold_fields (fun acc fn ((_tn, tp), p) ->
       match fn, p with
       | _, Some p -> check_pat env flex acc tp p
       | Field_named s, None -> check_pat_var env acc tp s
       | Field_positional _, None -> assert false) SymMap.empty params in
     let env' = env_cons env (Evals vs) in
     let res = check_or_infer env' flex ret body in
     let ty = cons_typ Pos (Func (map_fields (fun _fn ((tn,_tp),_p) -> tn) params, res)) in
     wf_typ Pos env ty; (* no dependency for now! Probably never, inferred. *)
(*     let ty = Type_simplification.canonise env flex ty in*)
     let ty = Type_simplification.remove_joins env flex ty in
     let envgc, ty = Type_simplification.garbage_collect env flex ty in
     wf_typ Pos envgc ty;
     let ty = generalise envgc (envgc.level, envgc.marker) ty in
     wf_typ Pos orig_env ty;
     ty
  | App (f, args) ->
     let fty = infer env flex f in
     let args = map_fields (fun _fn e -> e, ref (Tcons Top)) args in
     let res = ref (Tcons Bot) in
     let argtmpl = map_fields (fun _fn (_e, r) -> r) args in
     match_type env flex fty (Func (argtmpl, res)) |> report;
     fold_fields (fun () _fn (e, r) ->
         let r = !r in
         let e = match e with None -> failwith "punning?!" | Some e -> e in
         check env e r
       ) () args;
     !res

and bind env flex acc ps es =
  (* FIXME: replace this with subtype_cons_fields
     Need subtype_cons_fields to fold an accum,
     report errors some other way (err -> unit?) *)
  let _ps_open = (ps.fopen = `Open) in
  let bind_one acc fn (p,pty) e =
    let ty = check_or_infer_field env flex fn pty e in
    check_pat_field env flex acc ty fn p in
  let acc =
    fold2_fields acc ps es
      ~left:(fun _acc _fn _p -> failwith "extra patterns")
      ~right:(fun _acc _fn _e -> failwith "extra values FIXME open")
      ~both:bind_one in
  acc

and check_pat_var _env acc ty s =
  if SymMap.mem s acc then
    failwith "duplicate bindings"
  else
    SymMap.add s ty acc

and check_pat_field env flex acc (ty : typ) fn p =
  match fn, p with
  | Field_positional _, None -> assert false (* no positional punning *)
  | _, Some p -> check_pat env flex acc ty p
  | Field_named s, None -> check_pat_var env acc ty s

and check_pat env flex acc ty = function
  | None, _ -> failwith "bad pat"
  | Some p, _ -> check_pat' env flex acc ty p
and check_pat' env flex acc ty = function
  | Pvar (s,_) -> check_pat_var env acc ty s
  | Ptuple tp -> check_pat_untyped_fields env flex acc ty tp
  | Pparens p -> check_pat env flex acc ty p

and check_pat_typed_fields env acc ptypes fs =
  (* FIXME: I think this also just needs subtype_cons_fields to fold? *)
  let fs = map_fields (fun _fn (p,ty) -> p, ty, ref None) fs in
  let trec : _ tuple_fields =
    map_fields (fun _fn (_p, ty, r) ->
      match ty with
      | None -> r
      | Some _t -> failwith "unimp asc") fs in
  subtype_cons_fields Pos ptypes trec (fun pol _fn p r ->
    assert (!r = None);
    wf_typ pol env p;
    r := Some p;
    []) |> report;
  fold_fields (fun acc fn (p, _ty, r) ->
    let r = match !r with Some r -> r | None -> failwith "check_pat match?" in
    let flex = (-1,ref()) in    (* FIXME hack. I think this can trigger on weird pats. *)
    check_pat_field env flex acc r fn p) acc fs

and check_pat_untyped_fields env flex acc ty fs =
  let fs = map_fields (fun _fn p -> p, ref (Tcons Bot)) fs in
  let trec : _ tuple_fields = map_fields (fun _fn (_p, r) -> r) fs in
  match_type env flex ty (Record trec) |> report;
  fold_fields (fun acc fn (p, r) ->
    let r = !r in
    check_pat_field env flex acc r fn p) acc fs

and infer_lit = function
  | l, _ -> infer_lit' l
and infer_lit' = function
  | Bool _ -> cons_typ Pos Bool
  | Int _ -> cons_typ Pos Int
  | String _ -> cons_typ Pos String

and infer_fields env flex fs =
  map_fields (fun fn (e, ty) -> check_or_infer_field env flex fn ty e) fs

and check_or_infer env flex ty e =
  match ty with
  | None ->
     infer env flex e
  | Some ty ->
     let (tn, tp) = typ_of_tyexp env ty in
     check env e tn;
     tp

and check_or_infer_field env flex fn ty e =
  match fn, ty, e with
  | _, None, Some e ->
     infer env flex e
  | _, Some ty, Some e ->
     let (tn, tp) = typ_of_tyexp env ty in
     check env e tn;
     tp
  | Field_positional _, _, None ->
     assert false (* no positional punning *)
  | Field_named s, None, None ->
     env_lookup_var env { label = s; shift = 0 }
  | Field_named s, Some ty, None ->
     let (tn, tp) = typ_of_tyexp env ty in
     let tv = env_lookup_var env { label = s; shift = 0 } in
     subtype env tv tn |> report;
     tp

and check_annot env annot ty =
  wf_typ Neg env ty;
  match annot with
  | None -> ty
  | Some ty' ->
     let tn, tp = typ_of_tyexp env ty' in
     subtype env tp ty |> report;
     tn
