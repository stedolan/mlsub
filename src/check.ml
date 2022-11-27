open Util
open Tuple_fields
open Exp
open Typedefs
open Types

type error_kind =
  | Syntax
  | Bad_name of [`Unknown|`Duplicate] * [`Type|`Var] * string
  | Illformed_type of [`Join_multi_cons | `Join_not_cons_or_var | `Join_poly | `Bound_not_simple | `Bound_not_cons | `Bound_crosses_levels of string]
  | Conflict of [`Expr|`Pat|`Subtype] * Types.subtyping_error

exception Fail of Location.t * error_kind
let fail loc k = raise (Fail (loc, k))

let or_raise kind loc = function
  | Ok () -> ()
  | Error c -> fail loc (Conflict (kind, c))

let pp_err input loc err : PPrint.document =
  let open PPrint in
  let pp fmt = Format.ksprintf PPrint.utf8string fmt in
  let pp_ty ~env t =
    Typedefs.unparse_gen_typ t
      ~env
      ~neg:(fun ~env:_ () -> Typedefs.(mktyexp (named_type "_")))
      ~pos:(fun ~env:_ () -> Typedefs.(mktyexp (named_type "_")))
    |> Print.tyexp
  in
  let pp_loc (loc : Location.t) =
    (* FIXME character numbers also *)
    pp "%s:%d" loc.loc_start.pos_fname loc.loc_start.pos_lnum in
  let pp_context (loc : Location.t) =
    if loc.loc_start.pos_lnum = 0 then empty else
      let line = List.nth input (loc.loc_start.pos_lnum - 1) in
      let offs = loc.loc_start.pos_cnum - loc.loc_start.pos_bol in
      let cend =
        if loc.loc_end.pos_lnum = loc.loc_start.pos_lnum then
          loc.loc_end.pos_cnum - loc.loc_start.pos_bol 
        else
          String.length line in
      pp "%s" line ^^
      hardline ^^ pp "%*s" cend (String.make (cend-offs) '^')
  in
  (* FIXME: more of these could use context *)
  pp_loc loc ^^ pp ": " ^^ match err with
  | Syntax -> pp "syntax error"
  | Bad_name (err,kind,name) ->
     pp "%s %s name: %s"
       (match err with `Unknown -> "Unknown" | `Duplicate -> "Duplicate")
       (match kind with `Type -> "type" | `Var -> "variable")
       name
  | Illformed_type `Join_multi_cons ->
     pp "Joins may only contain one non-variable type"
  | Illformed_type `Join_not_cons_or_var ->
     pp "Joins may only contain constructed types and variables"
  | Illformed_type `Join_poly ->
     pp "Joins may not contain polymorphic types"
  | Illformed_type `Bound_not_simple ->
     pp "Bounds must be simple types"
  | Illformed_type `Bound_not_cons ->
     pp "Bounds must be constructed types"
  | Illformed_type (`Bound_crosses_levels n) ->
     pp "Rigid variable %s not allowed in join with variable bound earlier" n
  | Conflict (_kind, err) ->
     let env = err.env in
     let conflict =
       match err.err with
        | Incompatible ->
           pp "Type error"
        (* FIXME improve tuple field names *)
        | Fields (`Missing name) ->
           pp "The field '%s' is missing." (Tuple_fields.string_of_field_name name)
        | Fields (`Extra (Some name)) ->
           pp "A surplus field '%s' is present." (Tuple_fields.string_of_field_name name)
        | Fields (`Extra None) ->
           pp "Surplus fields are present."
        | Args (`Missing name) ->
           pp "The argument '%s' is missing." (Tuple_fields.string_of_field_name name)
        | Args (`Extra (Some name)) ->
           pp "A surplus argument '%s' is present." (Tuple_fields.string_of_field_name name)
        | Args (`Extra None) ->
           pp "Surplus arguments are present."
     in
     conflict ^^
     nest 2 (hardline ^^ pp_context loc) ^^
     nest 2 (hardline ^^ pp "   found:" ^^ group (nest 3 (break 1 ^^ pp_ty ~env err.lhs))) ^^
     nest 2 (hardline ^^ pp "expected:" ^^ group (nest 3 (break 1 ^^ pp_ty ~env err.rhs))) ^^
     (match err.located with
      | None -> empty
      | Some ((lty,lloc),(rty,rloc)) ->
         let lty = nest 4 (break 1 ^^ pp_ty ~env lty) ^^ break 1 in
         let rty = nest 4 (break 1 ^^ pp_ty ~env rty) ^^ break 1 in
         let l_interest = not (Location.subset lloc loc) in
         let r_interest = not (Location.subset rloc loc) in
         match l_interest, r_interest with
         | true, true ->
           hardline ^^
           group (pp "This" ^^ lty ^^ pp "comes from " ^^ pp_loc lloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context lloc) ^^
           hardline ^^
           group (pp "but is used as" ^^ rty ^^ pp "at " ^^ pp_loc rloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context rloc)
         | true, false ->
           hardline ^^
           group (pp "This" ^^ lty ^^ pp "comes from " ^^ pp_loc lloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context lloc) ^^
           hardline ^^
           group (pp "but is used as" ^^ rty)
         | false, true ->
           hardline ^^
           group (pp "This" ^^ lty ^^ pp "is used as" ^^ rty ^^ pp "at " ^^ pp_loc rloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context rloc)
         | false, false -> empty
     )

let rec env_lookup_var env v =
  match env with
  | Env_nil -> Error (Bad_name (`Unknown, `Var, v.label))
  | Env_vals { vals = vs; rest; _ }
       when SymMap.mem v.label vs ->
     if v.shift = 0 then Ok (SymMap.find v.label vs) else
       env_lookup_var rest { v with shift = v.shift - 1 }
  | Env_types { rest; _ } | Env_vals {rest; _}->
     env_lookup_var rest v

let env_lookup_type_var env lvl name =
  match env_lookup_type_var env name with
  | Some v ->
     if not (Env_level.extends v.level lvl) then
       Error (Illformed_type (`Bound_crosses_levels name))
     else
       Ok v
  | None -> Error (Bad_name (`Unknown, `Type, name))

let syn_tjoin loc (a : (_, _) typ) (b : (_, _) typ) =
  let rec join conses keep = function
    | Ttop l :: _ -> Ttop l
    | Tjoin (a, b) :: rest -> join conses keep (a :: b :: rest)
    | (Tsimple _ | Tvar _) as k :: rest -> join conses (k :: keep) rest
    | Tcons c :: rest when Cons.is_bottom c -> join conses keep rest
    | Tcons c :: rest -> join (c :: conses) keep rest
    | Tpoly _ :: _ -> fail loc (Illformed_type `Join_poly)
    | [] ->
       let conses = List.rev conses in
       let keep = List.rev keep in
       let joinands =
         match conses with
         | [] -> keep
         | [c] -> Tcons c :: keep
         | c :: cs ->
            let c =
              List.fold_left (fun c1 c2 ->
                let c = Cons.join c1 c2 in
                let either : _ Cons.One_or_two.t -> _ = function
                  | L x | R x -> x
                  | LR _ ->
                     fail loc (Illformed_type `Join_multi_cons)
                in
                Cons.map ~pos:either ~neg:either c) c cs
            in
            Tcons c :: keep
       in
       List.fold_left tjoin (List.hd joinands) (List.tl joinands)
  in
  join [] [] [a;b]

let tcons loc cons = Tcons (Cons.make ~loc cons)

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
        match env_lookup_type_var env lvl name with
        | Ok v -> Tvar (Some loc, Vrigid v)
        | Error e -> fail loc e
     end
  | Trecord fields ->
     tcons loc (Record (typs_of_tuple_tyexp env lvl fields))
  | Tfunc (args, res) ->
     tcons loc (Func (typs_of_tuple_tyexp env lvl args, typ_of_tyexp env lvl res))
  | Tparen t ->
     typ_of_tyexp env lvl t
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
    |> List.map (fun (name,_) -> {name; upper=None})
    |> IArray.of_list in
  let mkbound rig_names _loc bound =
    match bound with
    | None -> None
    | Some b ->
       let temp_env = Env_types { level; rig_names; rig_defns = stubs; rest = env } in
       let bound = close_typ_rigid ~ispos:false level (typ_of_tyexp temp_env (env_level temp_env) b) in
       begin match bound with Tcons _ -> () | _ -> fail (snd b) (Illformed_type `Bound_not_cons) end;
       if not (check_simple bound) then fail (snd b) (Illformed_type `Bound_not_simple);
       Some bound
  in
  let name_ix, vars = IArray.map_fold_left (fun names ((name',loc) as name, bound) ->
    let names' = SymMap.add name' (SymMap.find name' name_ix) names in
    names', (name, mkbound names loc bound)) SymMap.empty (IArray.of_list vars) in
  vars, name_ix

let typ_of_tyexp env t = typ_of_tyexp env (env_level env) t

let unit loc = tcons loc (Record (Tuple_fields.collect_fields []))

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

let fixpoint_iters = ref 0
let verbose_types = match Sys.getenv "VERBOSE_TYPES" with _ -> true | exception Not_found -> false

let elab_gen (env:env) ~mode poly (fn : env -> ptyp * 'a elab * _) : ptyp * (typolybounds option * tyexp * 'a) elab * bool =
  let rigvars', rig_names =
    match poly with
    | None -> IArray.empty, SymMap.empty
    | Some poly -> enter_polybounds env poly in

  let env', rigvars = enter_rigid env rigvars' rig_names in
  let orig_ty, Elab (erq, ek), gen_level = fn env' in
  wf_ptyp env' orig_ty;
  (* Format.printf "ELAB %a{\n%a}@." dump_ptyp orig_ty pp_elab_req erq; *)
  let can_generalise =
    match gen_level with
    | None -> true
    | Some lvl when Env_level.equal lvl (env_level env') -> true
    | lvl ->
       mark_var_use_at_level ~mode lvl;
       false
  in
  let rec fixpoint visit erq prev_ty =
    if verbose_types then Format.printf "FIX: %a" dump_ptyp orig_ty;
    if visit > 99 then intfail "looping?";
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
  (* Format.printf "ELAB2 %a{\n%a}@." dump_ptyp ty pp_elab_req erq; *)
  let policy = if can_generalise then `Generalise else `Hoist env in
  let ty = substn_ptyp ~mode:`Poly ~policy ~visit ~bvars ~env:env' ~index:0 ty in
  (* Format.printf "GEN: %a\n --> %a\n%!" dump_ptyp orig_ty pp_ptyp ty; *)
  let erq = elabreq_map_typs erq ~index:0
              ~neg:(substn_ntyp ~mode:`Elab ~policy ~visit ~bvars ~env:env')
              ~pos:(substn_ptyp ~mode:`Elab ~policy ~visit ~bvars ~env:env') in
  (* Format.printf "ELAB3 %a{\n%a}@." dump_ptyp ty pp_elab_req erq; *)
  if Vector.length bvars = 0 then
    ty, Elab (Pair(Ptyp ty, erq), fun (t,e) -> None, t, ek e), can_generalise
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
      | Error _ -> name, Location.noloc
      | Ok _ -> mkname () in
    let bounds = bvars |> Vector.to_array |> Array.map (function Gen_rigid rv -> IArray.get rigvars' rv.var | Gen_flex (_,r) -> mkname (), Some r) |> IArray.of_array in
    let tpoly = Tpoly { vars = bounds; body = ty } in
    wf_ptyp env tpoly;
    tpoly,
    Elab (Gen{bounds; body=Pair(Ptyp ty, erq)}, fun (poly, (t,e)) -> Some poly, t, ek e),
    can_generalise

(* FIXME:
   Can't decide whether this makes types better or worse! *)
(*let elab_ptyp = function
  | Tsimple (Lower(fv, ctor)) as ty when is_bottom (Lower(Fvset.empty,ctor)) ->
     (match (fv :> flexvar list) with
      | [fv] -> Elab (Ntyp (Tsimple fv), fun x -> x)
      | _ -> Elab (Ptyp ty, fun x -> x))
  | ty ->
     Elab (Ptyp ty, fun x -> x)*)
  
let fresh_flow env =
  let fv = fresh_flexvar (env_level env) in
  Tsimple fv, Tsimple (of_flexvar fv)

type inspect_result =
  | Ipoly of (flex_lower_bound, flexvar) poly_typ
  | Icons of (ptyp, ntyp) Cons.t
  | Iother

let inspect = function
  | Tsimple _ ->
     (* bidirectional checking does not look inside Tsimple *)
     Iother
  | Tpoly p ->
     Ipoly p
  | Tcons c ->
     (match Cons.get_single c with Some c -> Icons c | _ -> Iother)
  | Ttop _ | Tvar _ | Tjoin _ -> Iother

let rec check env ~(mode : generalisation_mode) e (ty : ntyp) : exp elab =
  wf_ntyp env ty;
  match e with
  | None, loc -> fail loc Syntax
  | Some e, loc ->
     let* e = check' env ~mode loc e ty in
     Some e, loc
and check' env ~mode eloc e ty =
  match e, inspect ty with
  | If (e, ifso, ifnot), _ ->
     let* e = check env ~mode e (tcons (snd e) Bool)
     and* ifso = check env ~mode ifso ty
     and* ifnot = check env ~mode ifnot ty in
     If (e, ifso, ifnot)
  | Parens e, _ ->
     let* e = check env ~mode e ty in
     Parens e
  | Tuple ef, Icons (Record tf) ->
     let infer_typed env ((_,loc) as e) =
       let ty, e = infer env ~mode e in
       let* e = e and* ty = elab_ptyp ty in
       Some (Typed (e, ty)), loc in
     let merged =
       merge_fields ef tf
         ~both:(fun _fn e ty -> Some (check env ~mode e ty))
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
     let* e = check env ~mode e (tcons eloc (Record r)) in
     Proj (e, (field, loc))
  | Let (p, pty, e, body), _ ->
     let env, pty, e = check_binding env ~mode p pty e in
     let* e = e and* pty = elab_ptyp pty and* body = check env ~mode body ty in
     Let(p, Some pty, e, body)
  | Seq (e1, e2), _ ->
     let e1 = check env ~mode e1 (unit eloc) in
     let e2 = check env ~mode e2 ty in
     let* e1 = e1 and* e2 = e2 in Seq (e1, e2)
  (* FIXME should I combine Tpoly and Func? *)
  | Fn _ as f, Ipoly { vars; body } ->
     (* rigvars not in scope in body, so no rig_names *)
     let env', rigvars = enter_rigid env vars SymMap.empty in
     let body = open_typ_rigid rigvars body in
     check' env' ~mode eloc f body
     (* FIXME: Can there be flexvars used somewhere? Do they get bound/hoisted properly? *)
  | Fn (None, params, ret, body), Icons (Func (ptypes, rtype)) ->
     (* If poly <> None, then we should infer & subtype *)
     (* FIXME: do we need another level here? Does hoisting break things? *)
     let _, vals = check_parameters env params ptypes in
     let env' = Env_vals { vals; rest = env } in
     let* body = check env' ~mode body (check_annot env' ret rtype) in
     (* No elaboration. Arguably we could *delete* annotations here! *)
     Fn (None, params, ret, body)
  | FnDef ((s, sloc), fndef, body), _ ->
     let fmode = fresh_gen_mode () in
     let fty, fndef = infer_func_def env ~mode:fmode eloc fndef in
     mark_var_use_at_level ~mode fmode.gen_level_acc;
     let binding = {typ = fty; gen_level = fmode.gen_level_acc } in
     let env = Env_vals { vals = SymMap.singleton s binding; rest = env } in
     let body = check env ~mode body ty in
     let* fndef = fndef and* body = body in
     FnDef((s,sloc), fndef, body)
  | Pragma "true", Icons Bool -> elab_pure e
  | Pragma "false", Icons Bool -> elab_pure e
  | e, _ ->
     (* Default case: infer and subtype. *)
     (* FIXME: we probably shouldn't even attempt this on intro forms
        at the wrong type. e.g. checking (1,2) against int *)
     let ty', e = infer' ~mode env eloc e in
     subtype env ty' ty |> or_raise `Expr eloc;
     wf_ntyp env ty;
     let* e = e in e

and infer env ~(mode : generalisation_mode) : exp -> ptyp * exp elab = function
  | None, loc -> fail loc Syntax
  | Some e, loc ->
     let ty, e = infer' env ~mode loc e in
     wf_ptyp env ty;
     ty, (let* e = e in Some e, loc)
and infer' env ~mode eloc : exp' -> ptyp * exp' elab = function
  | Lit l -> infer_lit l
  | Var (id,loc) as e ->
     begin match env_lookup_var env id with
     | Ok v ->
        mark_var_use_at_level ~mode v.gen_level;
        v.typ, elab_pure e
     | Error e -> fail loc e
     end
  | Typed (e, ty) ->
     let t = typ_of_tyexp env ty in
     t, let* e = check env ~mode e t in Typed (e, ty)
  | Parens e ->
     let ty, e = infer env ~mode e in
     ty, let* e = e in Parens e
  | If (e, ifso, ifnot) ->
     let e = check env ~mode e (tcons (snd e) Bool)
     and tyso, ifso = infer env ~mode ifso
     and tynot, ifnot = infer env ~mode ifnot in
     join_ptyp env tyso tynot,
     let* e = e and* ifso = ifso and* ifnot = ifnot in
     If (e, ifso, ifnot)
  | Proj (e, (field, loc)) ->
     let ty, e = infer env ~mode e in
     let f = Field_named field in
     let (), tyf =
       match
        match_typ env ty eloc
         (Record { fields = FieldMap.singleton f ();
                   fnames = [Field_named field]; fopen = `Open })
       with
       | Ok (Record r) -> FieldMap.find f r.fields
       | Ok _ -> assert false
       | Error c -> fail eloc (Conflict (`Expr, c)) in
     tyf, let* e = e in Proj (e, (field, loc))
  | Tuple fields ->
     if fields.fopen = `Open then failwith "invalid open tuple ctor";
     let fields = map_fields (fun _fn e -> infer env ~mode e) fields in
     tcons eloc (Record (map_fields (fun _ (ty, _e) -> ty) fields)),
     let* fields = elab_fields (map_fields (fun _fn (_ty, e) -> e) fields) in
     Tuple fields
  | Pragma "bot" as e -> Tcons (Cons.bottom_loc eloc), elab_pure e
  | Pragma s -> failwith ("pragma: " ^ s)
  | Let (p, pty, e, body) ->
     let env, pty, e = check_binding env ~mode p pty e in
     let res, body = infer env ~mode body in
     res,
     let* e = e and* pty = elab_ptyp pty and* body = body in
     Let(p, Some pty, e, body)
  | Seq (e1, e2) ->
     let e1 = check env ~mode e1 (unit eloc) in
     let ty, e2 = infer env ~mode e2 in
     ty, let* e1 = e1 and* e2 = e2 in Seq(e1, e2)
  | Fn fndef ->
     let ty, fndef = infer_func_def env ~mode eloc fndef in
     ty, let* fndef = fndef in Fn fndef
  | FnDef ((s,sloc), fndef, body) ->
     let fmode = fresh_gen_mode () in
     let fty, fndef = infer_func_def env ~mode:fmode eloc fndef in
     mark_var_use_at_level ~mode fmode.gen_level_acc;
     let binding = {typ = fty; gen_level = fmode.gen_level_acc } in
     let env = Env_vals { vals = SymMap.singleton s binding; rest = env } in
     let res, body = infer env ~mode body in
     res,
     let* fndef = fndef and* body = body in
     FnDef((s,sloc), fndef, body)
  | App (f, args) ->
     let fty, f = infer env ~mode f in
     let tyargs, ((), tyret) =
       match
        match_typ env fty eloc (Func (args, ()))
       with
       | Ok (Func (a, r)) -> a, r
       | Ok _ -> assert false
       | Error e -> fail eloc (Conflict (`Expr, e)) in
     let args = map_fields (fun _fn (e, t) -> check env ~mode e t) tyargs in
     tyret,
     let* f = f and* args = elab_fields args in
     App(f, args)

and infer_func_def env ~mode eloc (poly, params, ret, body) : ptyp * func_def elab =
   if params.fopen = `Open then failwith "invalid ... in params";
   let ty, elab, _generalised =
     elab_gen env ~mode poly (fun env ->
       let params = map_fields (fun _fn (p, ty) ->
         match ty with
         | Some ty ->
            let ty = typ_of_tyexp env ty in
            (* check for contravariant joins *)
            ignore (close_typ_rigid ~ispos:false (env_level env) ty);
            (ty,ty), p, None
         | None ->
            fresh_flow env, p, Some (env_level env)) params in
       let ptys = map_fields (fun _fn ((_tn,tp), p, gen_level) -> check_pat env ~gen_level tp p) params in
       let _, vs = merge_bindings ptys in
       let env' = Env_vals { vals = vs; rest = env } in
       let bmode = fresh_gen_mode () in
       let res, body =
         match ret with
         | Some ty ->
            let ty = typ_of_tyexp env ty in
            ignore (close_typ_rigid ~ispos:true (env_level env) ty);
            ty, check env' ~mode:bmode body ty
         | None ->
            infer env' ~mode:bmode body in
       let _ = map_fields (fun _fn ((tn,tp),_,_) -> wf_ntyp env tn; wf_ptyp env tp) params in
       (* FIXME params or ptys? What happens if they disagree? *)
       tcons eloc (Func (map_fields (fun _fn ((tn,_tp),_,_) -> tn) params, res)),
       body, bmode.gen_level_acc) in
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
(*     let poly =
     let mark = if generalised then [] else [("NOPOLY", Location.mark), None] in
     match poly with
     | None -> if mark = [] then None else Some mark
     | Some p -> Some (mark @ p)
   in*)
   (poly, params, Some tret, body)
  

and merge_bindings bs =
  let merge k a b =
    match a, b with
    | x, None | None, x -> x
    | Some _, Some _ ->
       failwith ("duplicate bindings " ^ k) in
  map_fields (fun _fn (ty, _) -> ty) bs,
  fold_fields (fun acc _fn (_, b) ->
      SymMap.merge merge acc b) SymMap.empty bs

and check_pat env ~gen_level ty = function
  | None, _ -> failwith "bad pat"
  | Some p, loc -> check_pat' env ~gen_level ty loc p
and check_pat' env ~gen_level ty ploc = function
  | Pvar (s,_) -> ty, SymMap.singleton s {typ = ty; gen_level }
  | Pparens p -> check_pat env ~gen_level ty p
  | Ptuple fs ->
     let fs =
       (* FIXME: fvinst? *)
       match
        match_typ env ty ploc (Record fs)
       with
       | Ok (Record fs) -> fs
       | Ok _ -> assert false
       | Error e -> fail ploc (Conflict (`Pat, e)) in
     let fs = map_fields (fun _fn (p, t) -> check_pat env ~gen_level t p) fs in
     let fs, bindings = merge_bindings fs in
     tcons ploc (Record fs), bindings

and check_parameters env params ptypes =
  let merged =
    merge_fields params ptypes
      ~both:(fun _fn (p,aty) typ ->
        let ty, gen_level =
          match aty with
          | None ->
             typ, Some (env_level env)
          | Some ty ->
             let t = typ_of_tyexp env ty in
             subtype env typ t |> or_raise `Pat (snd ty);
             t, None in
        Some (check_pat env ~gen_level ty p))
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

and check_binding env ~mode p pty e =
  let pty, e, gen_level =
    match pty with
    | None ->
       let bmode = fresh_gen_mode () in
       let pty, e = infer env ~mode:bmode e in
       mark_var_use_at_level ~mode bmode.gen_level_acc;
       pty, e, bmode.gen_level_acc
    | Some ty ->
       let t = typ_of_tyexp env ty in
       t, check env ~mode e t, None
  in
  let pty, vs = check_pat env ~gen_level pty p in
  let env = Env_vals { vals = vs; rest = env } in
  env, pty, e

and check_annot env annot ty =
  wf_ntyp env ty;
  match annot with
  | None -> ty
  | Some ty' ->
     let t = typ_of_tyexp env ty' in
     subtype env t ty |> or_raise `Subtype (snd ty');
     t
