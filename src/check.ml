open Tuple_fields
open Exp
open Typedefs
open Types

let report = function
  | Incompatible (s,t) -> failwith (Printf.sprintf "incompat %s <: %s" s t)
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

let env_lookup_type_var env lvl name =
  match env_lookup_type_var env name with
  | Some v ->
     if not (Env_level.extends v.level lvl) then
       failwith ("rigvar " ^ name ^ " not allowed inside join with rigvar bound earlier");
     Some v
  | None -> None

let rec split_tjoin env lvl cons vars rest =
  match rest with
  | [] -> cons, List.rev vars
  | (None, _) :: _ -> failwith "type syntax error"
  | (Some ty, loc) as ty' :: rest ->
     match ty with
     | Tjoin (a, b) ->
        split_tjoin env lvl cons vars (a :: b :: rest)
     | Tparen a ->
        split_tjoin env lvl cons vars (a :: rest)
     | Tforall _ -> failwith "Tforall in join"
     | ty ->
        let as_var =
          match ty with
          | Tnamed (name, _) ->
             (* FIXME shifting? *)
             Option.map (fun v -> v, loc) (env_lookup_type_var env lvl name.label)
          | _ -> None in
        match as_var with
        | Some v -> split_tjoin env lvl cons (v :: vars) rest
        | None ->
           match cons with
           | None -> split_tjoin env lvl (Some ty') vars rest
           | Some _ -> failwith "multiple cons in join"

let tcons loc cons = Tcons (mk_cons_locs loc cons, cons)
     
let rec typ_of_tyexp : 'a 'b . env -> Env_level.t -> tyexp -> ('a, 'b) typ =
  fun env lvl ty -> match ty with
  | None, _ -> failwith "type syntax error"
  | Some t, loc -> typ_of_tyexp' env lvl loc t
and typ_of_tyexp' : 'a 'b . env -> Env_level.t -> Location.t -> tyexp' -> ('a, 'b) typ =
  fun env lvl loc ty -> match ty with
  | Tnamed (name, _) ->
     (* FIXME shifting? *)
     let name = name.label in
     begin match lookup_named_type name with
     | Some cons -> tcons loc cons
     | None ->
        match env_lookup_type_var env lvl name with
        | Some v -> Tvar (Location.single loc, Vrigid v)
        | None -> failwith ("unknown type " ^ name)
     end
  | Trecord fields ->
     tcons loc (Record (typs_of_tuple_tyexp env lvl fields))
  | Tfunc (args, res) ->
     tcons loc (Func (typs_of_tuple_tyexp env lvl args, typ_of_tyexp env lvl res))
  | Tparen t ->
     typ_of_tyexp env lvl t
  | Tjoin (a, b) ->
     let cons, rigvars = split_tjoin env lvl None [] [a;b] in
     let rigvars = List.stable_sort (fun ((v : rigvar),_) ((v' : rigvar),_) -> Env_level.compare v.level v'.level) rigvars in
     let join_lvl =
       match rigvars with
       | [] -> lvl
       | (rv,_) :: _ -> rv.level in
     let cloc, cons =
       match cons with
       | None -> Location.empty, Bot
       | Some c ->
          match typ_of_tyexp env join_lvl c with
          | Tcons (l, c) -> l, c
          | _ -> failwith "Expected a constructed type" in
     if rigvars <> [] && not (check_simple (Tcons (cloc, cons))) then
       failwith "Poly type under join";
     List.fold_left (fun c (r,l) -> Tvjoin (c, Location.single l, Vrigid r)) (Tcons (cloc, cons)) rigvars
  | Tforall (vars, body) ->
     let vars, name_ix = enter_polybounds env vars in
     let env, _rigvars = enter_rigid env vars name_ix in
     let body = close_typ_rigid ~ispos:true (env_level env) (typ_of_tyexp env (env_level env) body) in
     Tpoly { vars; body }

and typs_of_tuple_tyexp : 'a 'b . env -> Env_level.t -> tyexp tuple_fields -> ('a, 'b) typ tuple_fields =
  fun env lvl ts -> map_fields (fun _fn t -> typ_of_tyexp env lvl t) ts

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
    |> List.map (fun ((name,_),_) -> {name; upper={ctor={cons=Top;rigvars=Rvset.empty;cons_locs=[]};flexvars=[]}})
    |> IArray.of_list in
  let mkbound rig_names bound =
    match bound with
    | None -> Tcons (Location.empty, Top)
    | Some b ->
       let temp_env = Env_types { level; rig_names; rig_defns = stubs; rest = env } in
       let bound = close_typ_rigid ~ispos:false level (typ_of_tyexp temp_env (env_level temp_env) b) in
       if not (check_simple bound) then failwith "bounds must be simple";
       bound
  in
  let name_ix, vars = IArray.map_fold_left (fun names ((name,_), bound) ->
    let names' = SymMap.add name (SymMap.find name name_ix) names in
    names', (name, mkbound names bound)) SymMap.empty (IArray.of_list vars) in
  vars, name_ix

let typ_of_tyexp env t = typ_of_tyexp env (env_level env) t

let unit loc = tcons loc (Record (Tuple_fields.collect_fields []))

open Elab

let fixpoint_iters = ref 0
let verbose_types = match Sys.getenv "VERBOSE_TYPES" with _ -> true | exception Not_found -> false

let elab_gen (env:env) poly (fn : env -> ptyp * 'a elab) : ptyp * (typolybounds option * tyexp * 'a) elab =
  let rigvars', rig_names =
    match poly with
    | None -> IArray.empty, SymMap.empty
    | Some poly -> enter_polybounds env poly in

  let env', rigvars = enter_rigid env rigvars' rig_names in
  let orig_ty, Elab (erq, ek) = fn env' in
  wf_ptyp env' orig_ty;

  let rec fixpoint visit erq prev_ty =
    if verbose_types then Format.printf "FIX: %a" dump_ptyp orig_ty;
    if visit > 10 then intfail "looping?";
    let changes = ref [] in
    let ty = expand_ptyp visit ~changes env' prev_ty in
    wf_ptyp env' ty;
    let erq = elabreq_map_typs erq ~index:0
                ~neg:(fun ~index:_ -> expand_ntyp visit ~changes env')
                ~pos:(fun ~index:_ -> expand_ptyp visit ~changes env') in
    if verbose_types then Format.printf "CHANGED: %a\n\n" pp_changes !changes;
    if !changes = [] then
      (visit, erq, ty)
    else
      (incr fixpoint_iters; fixpoint (visit+2) erq ty) in
  let visit, erq, ty = fixpoint 2 erq orig_ty in
  (* Format.printf "FIXPOINT: %d\n" (visit/2); *)

  let bvars = Vector.create () in
  rigvars |> IArray.iter (fun rv -> ignore (Vector.push bvars (Gen_rigid rv)));

  let subst = { mode = `Poly; visit; bvars; level=env_level env'; index = 0 } in
  let ty = substn_ptyp subst ty in
  (* Format.printf "GEN: %a\n --> %a\n%!" dump_ptyp orig_ty pp_ptyp ty; *)
  let erq = elabreq_map_typs erq ~index:0
              ~neg:(fun ~index t -> substn_ntyp {subst with index; mode=`Elab} t)
              ~pos:(fun ~index t -> substn_ptyp {subst with index; mode=`Elab} t) in
  if Vector.length bvars = 0 then
    ty, Elab (Pair(Ptyp ty, erq), fun (t,e) -> None, t, ek e)
  else
    let next_name = ref 0 in
    let rec mkname () =
      let n = !next_name in
      incr next_name;
      let name = match n with
        | n when n < 26 -> Printf.sprintf "%c" (Char.chr (Char.code 'A' + n))
        | n -> Printf.sprintf "T_%d" (n-26) in
      (* NB: look up env', to ensure no collisions with rigvars *)
      match env_lookup_type_var env' (env_level env') name with
      | None -> name
      | Some _ -> mkname () in
    let bounds = bvars |> Vector.to_array |> Array.map (function Gen_rigid rv -> IArray.get rigvars' rv.var | Gen_flex (_,r) -> mkname (), r) |> IArray.of_array in
    let tpoly = Tpoly { vars = bounds; body = ty } in
    wf_ptyp env tpoly;
    tpoly,
    Elab (Gen{bounds; body=Pair(Ptyp ty, erq)}, fun (poly, (t,e)) -> Some poly, t, ek e)
  
let fresh_flow env =
  let fv = fresh_flexvar (env_level env) in
  Tvar (Location.empty, Vflex fv)

let rec check env e (ty : ntyp) : exp elab =
  wf_ntyp env ty;
  match e with
  | None, _ -> failwith "bad exp"
  | Some e, loc ->
     let* e = check' env loc e ty in
     Some e, loc
and check' env eloc e ty =
  match e, ty with
  | If (e, ifso, ifnot), _ ->
     let* e = check env e (tcons eloc Bool)
     and* ifso = check env ifso ty
     and* ifnot = check env ifnot ty in
     If (e, ifso, ifnot)
  | Parens e, _ ->
     let* e = check env e ty in
     Parens e
  | Tuple ef, Tcons (tloc, Record tf) ->
     let infer_typed env ((_,loc) as e) =
       let ty, e = infer env e in
       let* e = e and* ty = elab_ptyp ty in
       Some (Typed (e, ty)), loc in
     let merged =
       merge_fields ef tf
         ~both:(fun _fn e ty -> Some (check env e ty))
         ~left:(fun _fn e -> Some (infer_typed env e))
         ~right:(fun fn _ty -> failwith ("missing " ^ string_of_field_name fn) )
         ~extra:(function
           | _, (`Closed, `Extra) -> failwith "extra"
           | (`Open, _), _ -> failwith "invalid open tuple ctor" (* no open tuples *)
           | (`Closed, `Extra), _ -> failwith "missing"
           | _ -> `Closed) in
     let* ef = elab_fields merged in
     Tuple ef
  | Proj (e, (field, loc)), _ ->
     (* Because of subtyping, there's a checking form for Proj! *)
     let r = { fields = FieldMap.singleton (Field_named field) ty;
               fnames = [Field_named field];
               fopen = `Open } in
     let* e = check env e (tcons eloc (Record r)) in
     Proj (e, (field, loc))
  | Let (p, pty, e, body), _ ->
     let pty, e = check_or_infer env pty e in
     let pty, vs = check_pat env pty p in
     let env = Env_vals { vals = vs; rest = env } in
     let* e = e and* pty = elab_ptyp pty and* body = check env body ty in
     Let(p, Some pty, e, body)
  | Seq (e1, e2), ty ->
     let e1 = check env e1 (unit eloc) in
     let e2 = check env e2 ty in
     let* e1 = e1 and* e2 = e2 in Seq (e1, e2)
  (* FIXME should I combine Tpoly and Func? *)
  | Fn _ as f, Tpoly { vars; body } ->
     (* rigvars not in scope in body, so no rig_names *)
     let env', rigvars = enter_rigid env vars SymMap.empty in
     let body = open_typ_rigid rigvars body in
     check' env' eloc f body
     (* FIXME: Can there be flexvars used somewhere? Do they get bound/hoisted properly? *)
  | Fn (None, params, ret, body), Tcons (tloc, Func (ptypes, rtype)) ->
     (* If poly <> None, then we should infer & subtype *)
     (* FIXME: do we need another level here? Does hoisting break things? *)
     let _, vals = check_parameters env params ptypes in
     let env' = Env_vals { vals; rest = env } in
     let* body = check env' body (check_annot env' ret rtype) in
     (* No elaboration. Arguably we could *delete* annotations here! *)
     Fn (None, params, ret, body)
  | Pragma "true", Tcons (_,Bool) -> elab_pure e
  | Pragma "false", Tcons (_,Bool) -> elab_pure e
  | e, _ ->
     (* Default case: infer and subtype. *)
     let ty', e = infer' env eloc e in
     subtype ~error:report env ty' ty;
     wf_ntyp env ty;
     let* e = e in e

and infer env : exp -> ptyp * exp elab = function
  | None, _ -> failwith "bad exp"
  | Some e, loc ->
     let ty, e = infer' env loc e in
     wf_ptyp env ty;
     ty, (let* e = e in Some e, loc)
and infer' env eloc : exp' -> ptyp * exp' elab = function
  | Lit l -> infer_lit l
  | Var (id, _loc) as e -> env_lookup_var env id, elab_pure e
  | Typed (e, ty) ->
     let t = typ_of_tyexp env ty in
     t, let* e = check env e t in Typed (e, ty)
  | Parens e ->
     let ty, e = infer env e in
     ty, let* e = e in Parens e
  | If (e, ifso, ifnot) ->
     let e = check env e (tcons eloc Bool)
     and tyso, ifso = infer env ifso
     and tynot, ifnot = infer env ifnot in
     join_ptyp env tyso tynot,
     let* e = e and* ifso = ifso and* ifnot = ifnot in
     If (e, ifso, ifnot)
  | Proj (e, (field, loc)) ->
     let ty, e = infer env e in
     let f = Field_named field in
     let (), tyf =
       match_typ ~error:report env ty eloc
         (Record { fields = FieldMap.singleton f ();
                   fnames = [Field_named field]; fopen = `Open })
       |> function Record r -> FieldMap.find f r.fields | _ -> assert false in
     tyf, let* e = e in Proj (e, (field, loc))
  | Tuple fields ->
     if fields.fopen = `Open then failwith "invalid open tuple ctor";
     let fields = map_fields (fun _fn e -> infer env e) fields in
     tcons eloc (Record (map_fields (fun _ (ty, _e) -> ty) fields)),
     let* fields = elab_fields (map_fields (fun _fn (_ty, e) -> e) fields) in
     Tuple fields
  | Pragma "bot" as e -> tcons eloc Bot, elab_pure e
  | Pragma s -> failwith ("pragma: " ^ s)
  | Let (p, pty, e, body) ->
     let pty, e = check_or_infer env pty e in
     let pty, vals = check_pat env pty p in
     let env = Env_vals { rest=env; vals } in
     let res, body = infer env body in
     res,
     let* e = e and* pty = elab_ptyp pty and* body = body in
     Let(p, Some pty, e, body)
  | Seq (e1, e2) ->
     let e1 = check env e1 (unit eloc) in
     let ty, e2 = infer env e2 in
     ty, let* e1 = e1 and* e2 = e2 in Seq(e1, e2)
  | Fn (poly, params, ret, body) ->
     if params.fopen = `Open then failwith "invalid ... in params";
     let ty, elab =
       elab_gen env poly (fun env ->
         let params = map_fields (fun _fn (p, ty) ->
           match ty with
           | Some ty ->
              let ty = typ_of_tyexp env ty in
              (* check for contravariant joins *)
              ignore (close_typ_rigid ~ispos:false (env_level env) ty);
              ty, p
           | None -> fresh_flow env, p) params in
         let ptys = map_fields (fun _fn (t, p) -> check_pat env t p) params in
         let _, vs = merge_bindings ptys in
         let env' = Env_vals { vals = vs; rest = env } in
         let res, body =
           match ret with
           | Some ty ->
              let ty = typ_of_tyexp env ty in
              ignore (close_typ_rigid ~ispos:true (env_level env) ty);
              ty, check env' body ty
           | None ->
              infer env' body in
         let _ = map_fields (fun _fn (t,_) -> wf_ntyp env t) params in
         (* FIXME params or ptys? What happens if they disagree? *)
         tcons eloc (Func (map_fields (fun _fn (t,_) -> t) params, res)),
         body) in
     ty,
     let* poly, ty, body = elab in
     let tparams, tret =
       match ty with
       | Some (Tfunc (p,r)), _ -> p, r
       | ty -> intfail "what? %a" pp_tyexp ty in
     let params =
       merge_fields params tparams
         ~left:(fun _ _ -> assert false)
         ~right:(fun _ _-> assert false)
         ~both:(fun _fn (p, _) t -> Some (p, Some t))
         ~extra:(fun ((c, _),_) -> c) in
     Fn (poly, params, Some tret, body)
  | App (f, args) ->
     let fty, f = infer env f in
     let tyargs, ((), tyret) =
       match_typ ~error:report env fty eloc (Func (args, ()))
       |> function Func (a,r) -> a,r | _ -> assert false in
     let args = map_fields (fun _fn (e, t) -> check env e t) tyargs in
     tyret,
     let* f = f and* args = elab_fields args in
     App(f, args)

and merge_bindings bs =
  let merge k a b =
    match a, b with
    | x, None | None, x -> x
    | Some _, Some _ ->
       failwith ("duplicate bindings " ^ k) in
  map_fields (fun _fn (ty, _) -> ty) bs,
  fold_fields (fun acc _fn (_, b) ->
      SymMap.merge merge acc b) SymMap.empty bs

and check_pat env ty = function
  | None, _ -> failwith "bad pat"
  | Some p, loc -> check_pat' env ty loc p
and check_pat' env ty ploc = function
  | Pvar (s,_) -> ty, SymMap.singleton s ty
  | Pparens p -> check_pat env ty p
  | Ptuple fs ->
     let fs =
       match_typ ~error:report env ty ploc (Record fs)
       |> function Record fs -> fs | _ -> assert false in
     let fs = map_fields (fun _fn (p, t) -> check_pat env t p) fs in
     let fs, bindings = merge_bindings fs in
     tcons ploc (Record fs), bindings

and check_parameters env params ptypes =
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
        Some (check_pat env ty p))
      ~left:(fun _fn (_p, _aty) -> failwith "extra param")
      ~right:(fun _fn _typ -> failwith "missing param")
      ~extra:(fun _ -> `Closed) in
  merge_bindings merged

and infer_lit = function
  | l, loc -> infer_lit' loc l, elab_pure (Lit (l, loc))
and infer_lit' loc = function
  | Bool _ -> tcons loc Bool
  | Int _ -> tcons loc Int
  | String _ -> tcons loc String

and check_or_infer env ty e : ptyp * exp elab =
  match ty with
  | None ->
     infer env e
  | Some ty ->
     let t = typ_of_tyexp env ty in
     t, check env e t

and check_annot env annot ty =
  wf_ntyp env ty;
  match annot with
  | None -> ty
  | Some ty' ->
     let t = typ_of_tyexp env ty' in
     subtype ~error:report env t ty;
     t
