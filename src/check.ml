open Exp
open Typedefs
open Types

let env0 = env_cons Env_empty Egen

let unimp () = failwith "unimplemented"

let pos_field_name i = "$" ^ string_of_int i

(* Returns a A⁻ ≤ A⁺ pair *)
let rec typ_of_tyexp env = function
  | None, _ -> failwith "bad type"
  | Some t, _ -> typ_of_tyexp' env t
and typ_of_tyexp' env : tyexp' -> typ * typ = function
  | Tnamed ({label="any";_}, _) ->
     cons_typ Neg Top, cons_typ Pos Top
  | Tnamed ({label="nothing";_}, _) ->
     cons_typ Neg Bot, cons_typ Pos Bot
  | Tnamed ({label="int";_}, _) ->
     cons_typ Neg Int, cons_typ Pos Int
  | Tnamed ({label="string";_}, _) ->
     cons_typ Neg String, cons_typ Pos String
  | Tnamed _ -> assert false
  | Tforall (vars, body) -> assert false
  | Trecord (fields, cl) ->
     let ns, ps = typs_of_tuple_tyexp env fields cl in
     cons_typ Neg (Record ns), cons_typ Pos (Record ps)
  | Tfunc (args, res) ->
     let ans, aps = typs_of_tuple_tyexp env args `Closed in
     let rn, rp = typ_of_tyexp env res in
     cons_typ Neg (Func (aps, rn)), cons_typ Pos (Func (ans, rp))
  | Tparen t ->
     typ_of_tyexp env t
  | Tjoin (s, t) ->
     assert false
  | Tmeet (s, t) ->
     assert false

and typs_of_tuple_tyexp env fields cl = match fields with
  | None, _ -> failwith "bad tuple of types"
  | Some t, _ -> typs_of_tuple_tyexp' env t cl
and typs_of_tuple_tyexp' env t cl =
  let posid = ref 0 in
  let fields = t |> List.fold_left (fun fields f ->
    let s, d = match f with
      | TFpositional d ->
         let r = pos_field_name !posid in
         incr posid;
         (r, d)
      | TFnamed ((s,_), d) ->
         (s, d) in
    if StrMap.mem s fields then
      failwith ("duplicate field names " ^ s);
    StrMap.add s (typ_of_tyexp env d) fields
  ) StrMap.empty in
  (StrMap.map fst fields, cl), (StrMap.map snd fields, cl)


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
   | Missing k -> failwith ("missing " ^ k)
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
  | Tuple fields, Tm_cons (Record (tfields, cl)) ->
     let fields = match fields with Some f, _ -> f | _ -> failwith "bad" in
     let remaining, _ =
       List.fold_left (fun (remaining,npos) field ->
       let (fname,ty,e,npos) =
         match field with
         | Fpositional (ty, e) ->
            pos_field_name npos, ty, e, npos + 1
         | Fnamed ((s,_sloc), ty, Some e) ->
            s, ty, e, npos
         | Fnamed (_s, _ty, None) ->
            failwith "punning not supported yet" in
       if not (StrMap.mem fname remaining) then begin
         if StrMap.mem fname tfields then
           failwith "duplicate fields"
         else
           failwith "unexpected field"
       end else begin
         check_or_check env e ty (StrMap.find fname remaining);
         let remaining = StrMap.remove fname remaining in
         (remaining, npos)
       end) (tfields, 0) fields in
     if not (StrMap.is_empty remaining) then
       failwith "extra fields";
     ()
  | e, ty ->
     (* Default case: infer and subtype *)
     let ty' = infer' env e in
     match_type env Pos ty' ty |> report

and infer env = function
  | None, _ -> failwith "bad exp"
  | Some e, _ -> infer' env e
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
     match_type env Pos ty (Tm_cons (Record (StrMap.singleton field (Tm_unknown res), `Open))) |> report;
     !res
  | Tuple fields ->
     cons_typ Pos (Record (infer_fields env fields, `Closed))
  | _ -> assert false

and infer_lit = function
  | l, _ -> infer_lit' l
and infer_lit' = function
  | Bool _ -> cons_typ Pos Bool
  | Int _ -> cons_typ Pos Int
  | String _ -> cons_typ Pos String

and infer_fields env = function
  | None, _ -> failwith "bad tuple"
  | Some fs, _ -> infer_fields' env fs  
and infer_fields' env fs =
  let fields, _ = List.fold_left (fun (fields, npos) f ->
    match f with
    | Fpositional (ty, e) ->
       let fields =
         StrMap.add (pos_field_name npos) (infer_or_check env e ty) fields in
       fields, npos+1
    | Fnamed ((s,_sloc), ty, e) ->
       if StrMap.mem s fields then
         failwith "dup field name";
       let e = match e with
         | Some e -> e
         | None -> failwith "punning later" in
       let fields =
         StrMap.add s (infer_or_check env e ty) fields in
       fields, npos) (StrMap.empty, 0) fs in
  fields

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
