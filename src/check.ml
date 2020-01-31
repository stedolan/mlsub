open Exp
open Typedefs
open Types

let env0 = env_cons Env_empty Egen

let unimp () = failwith "unimplemented"

(* Returns a A⁻ ≤ A⁺ pair *)
let rec typ_of_tyexp env = function
  | None, _ -> failwith "bad type"
  | Some t, _ -> typ_of_tyexp' env t
and typ_of_tyexp' env : tyexp' -> typ * typ = function
  | Tnamed ({label="any";_}, _) ->
     cons_typ Neg Top, cons_typ Pos Top
  | Tnamed ({label="nothing";_}, _) ->
     cons_typ Neg Bot, cons_typ Pos Bot
  | Tnamed ({label="bool";_}, _) ->
     cons_typ Neg Bool, cons_typ Pos Bool
  | Tnamed ({label="int";_}, _) ->
     cons_typ Neg Int, cons_typ Pos Int
  | Tnamed ({label="string";_}, _) ->
     cons_typ Neg String, cons_typ Pos String
  | Tnamed _ -> assert false
  | Tforall (_vars, _body) -> unimp ()
  | Trecord fields ->
     let ns, ps = typs_of_tuple_tyexp env fields in
     cons_typ Neg (Record ns), cons_typ Pos (Record ps)
  | Tfunc (args, res) ->
     let ans, aps = typs_of_tuple_tyexp env args in
     let rn, rp = typ_of_tyexp env res in
     cons_typ Neg (Func (aps, rn)), cons_typ Pos (Func (ans, rp))
  | Tparen t ->
     typ_of_tyexp env t
  | Tjoin (_s, _t) -> unimp ()
  | Tmeet (_s, _t) -> unimp ()

(*and typs_of_tuple_tyexp env fields cl = match fields with
  | None, _ -> failwith "bad tuple of types"
  | Some t, _ -> typs_of_tuple_tyexp' env t cl*)
and typs_of_tuple_tyexp env t =
  let fpos = t.tyfields_pos |> List.map (typ_of_tyexp env) in
  let fnamed = t.tyfields_named |> List.fold_left (fun fields ((s,_), t) ->
    if StrMap.mem s fields then failwith ("duplicate field names " ^ s);
    StrMap.add s (typ_of_tyexp env t) fields) StrMap.empty in
  let fnames = t.tyfields_named |> List.map (fun ((s,_),_) -> s) in
  let fopen = t.tyfields_open in
  { fpos = List.map fst fpos;
    fnamed = StrMap.map fst fnamed;
    fnames; fopen },
  { fpos = List.map snd fpos;
    fnamed = StrMap.map snd fnamed;
    fnames; fopen }


let rec env_lookup_var env v =
  match env with
  | Env_empty -> failwith "not found"
  | Env_cons { entry = Eval (s, t); rest; _ } when s = v.label ->
     if v.shift = 0 then t else
       env_lookup_var rest { v with shift = v.shift - 1 }
  | Env_cons { rest; _ } ->
     env_lookup_var rest v


let report errs = List.iter (function
   | Incompatible -> failwith "incompat"
   | Missing (`Named k) -> failwith ("missing " ^ k)
   | Missing `Positional -> failwith ("missing pos")
   | Extra _ -> failwith ("extra")) errs

(* When checking a term against a template type,
   I think it's principal to inspect a Tm_typ as long as we don't
   inspect any styps. (???) 
   FIXME: this conflicts with the tendency of cons_typ to make styps. *)
let inspect = function
  | Tm_typ (Tcons cons) ->
     Tm_cons (map_head Neg (fun _pol x -> Tm_typ x) cons)
  | t -> t


let rec check env e (ty : template) =
  match e with
  | None, _ -> failwith "bad exp"
  | Some e, _ -> check' env e ty
and check' env e ty =
  let ty = inspect ty in (* ??? *)
  match e, ty with
  | If (e, ifso, ifnot), ty ->
     check env e (Tm_typ (cons_typ Neg Bool));
     check env ifso ty;
     check env ifnot ty
  | Parens e, ty ->
     check env e ty
  | Tuple fields, Tm_cons (Record tf) ->
     check_fields env fields tf
  | Pragma "true", Tm_cons Bool -> ()
  | Pragma "false", Tm_cons Bool -> ()
  | e, ty ->
     (* Default case: infer and subtype *)
     let ty' = infer' env e in
     match_type env Pos ty' ty |> report

and check_fields env ef tf =
  let rec check_pos es ts =
    match es, ts with
    | (e, ty) :: es, t :: ts ->
       check_or_check env e ty t; check_pos es ts
    | [], _::_ -> failwith "missing positional field"
    | _::_, [] -> failwith "too many positional fields. FIXME open tuples"
    | [], [] -> () in
  check_pos ef.fields_pos tf.fpos;
  let remaining = List.fold_left (fun remaining ((s, _), e, ty) ->
    let e = match e with Some e -> e | None -> failwith "punning later" in
    if not (StrMap.mem s remaining) then begin
      if StrMap.mem s tf.fnamed then
        failwith "duplicate fields"
      else
        failwith "unexpected field FIXME open tuples"
    end else begin
      check_or_check env e ty (StrMap.find s remaining);
      StrMap.remove s remaining
    end) tf.fnamed ef.fields_named in
  (* FIXME: ignores open/closed *)
  if not (StrMap.is_empty remaining) then
    failwith "extra fields";
  ()

and infer env = function
  | None, _ -> failwith "bad exp"
  | Some e, _ -> let ty = infer' env e in wf_typ Pos env ty; ty
and infer' env = function
  | Lit l -> infer_lit l
  | Var (id, _loc) -> env_lookup_var env id
  | Typed (e, ty) ->
     let tn, tp = typ_of_tyexp env ty in
     check env e (Tm_typ tn); tp
  | Parens e -> infer env e
  | If (e, ifso, ifnot) ->
     check env e (Tm_typ (cons_typ Neg Bool));
     let tyso = infer env ifso and tynot = infer env ifnot in
     (* FIXME: join of typ? *)
     Tsimple (Tstyp_simple (join Pos (approx env env Pos tyso) (approx env env Pos tynot)))
  | Proj (e, (field,_loc)) ->
     let ty = infer env e in
     let res = ref (cons_typ Pos (ident Pos)) in
     let tmpl = Tm_cons (Record { fpos = [];
                                  fnamed = StrMap.singleton field (Tm_unknown res);
                                  fnames = [field]; fopen = `Open }) in
     match_type env Pos ty tmpl |> report;
     !res
  | Tuple fields ->
     cons_typ Pos (Record (infer_fields env fields))
  | Pragma "bot" -> cons_typ Pos Bot
  | Pragma s -> failwith ("pragma: " ^ s)
  | _ -> assert false


and infer_lit = function
  | l, _ -> infer_lit' l
and infer_lit' = function
  | Bool _ -> cons_typ Pos Bool
  | Int _ -> cons_typ Pos Int
  | String _ -> cons_typ Pos String

and infer_fields env fs =
  let fpos = fs.fields_pos |> List.map (fun (e, ty) ->
    infer_or_check env e ty) in
  let fnamed = fs.fields_named |> List.fold_left (fun fields ((s, _), e, ty) ->
    let e = match e with Some e -> e | None -> failwith "punning unimplemented" in
    if StrMap.mem s fields then failwith "duplicate key";
    StrMap.add s (infer_or_check env e ty) fields) StrMap.empty in
  let fnames = fs.fields_named |> List.map (fun ((s, _), _, _) -> s) in
  let fopen = fs.fields_open in
  { fpos; fnamed; fnames; fopen }

and infer_or_check env e ty =
  match ty with
  | None -> infer env e
  | Some ty ->
     let tn, tp = typ_of_tyexp env ty in
     check env e (Tm_typ tn); tp

and check_or_check env e ty1 ty2 =
  match ty1 with
  | None -> check env e ty2
  | Some ty ->
     let tn, tp = typ_of_tyexp env ty in
     check env e (Tm_typ tn);
     match_type env Pos tp ty2 |> report

