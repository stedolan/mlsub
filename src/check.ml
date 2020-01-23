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
  | Tnamed ({label="int";_}, _) ->
     cons_typ Neg Int, cons_typ Pos Int
  | Tnamed ({label="string";_}, _) ->
     cons_typ Neg String, cons_typ Pos String
  | Tnamed _ -> assert false
  | Tforall (vars, body) -> assert false
  | Trecord (fields, `Closed) ->
     let ns, ps = typs_of_tuple_tyexp env fields in
     cons_typ Neg (Record ns), cons_typ Pos (Record ps)
  | Tfunc (args, res) ->
     let ans, aps = typs_of_tuple_tyexp env args in
     let rn, rp = typ_of_tyexp env res in
     cons_typ Neg (Func (aps, rn)), cons_typ Pos (Func (ans, rp))
  | Tparen t ->
     typ_of_tyexp env t
  | Tjoin (s, t) ->
     assert false
  | Tmeet (s, t) ->
     assert false

and typs_of_tuple_tyexp env = function
  | None, _ -> failwith "bad tuple of types"
  | Some t, _ -> typs_of_tuple_tyexp' env t
and typs_of_tuple_tyexp' env t =
  let posid = ref 0 in
  let fields = t |> List.fold_left (fun fields f ->
    let s, d = match f with
      | TFpositional d ->
         let r = "$" ^ string_of_int !posid in
         incr posid;
         (r, d)
      | TFnamed ((s,_), d) ->
         (s, d) in
    if StrMap.mem s fields then
      failwith ("duplicate field names " ^ s);
    StrMap.add s (typ_of_tyexp env d) fields
  ) StrMap.empty in
  StrMap.map fst fields, StrMap.map snd fields


let rec env_lookup_var env v =
  match env with
  | Env_empty -> failwith "not found"
  | Env_cons { entry = Eval (s, t); rest; _ } when s = v.label ->
     if v.shift = 0 then t else
       env_lookup_var rest { v with shift = v.shift - 1 }
  | Env_cons { rest; _ } ->
     env_lookup_var rest v


let report errs = List.iter (fun _ -> failwith "type error") errs

let rec check env e (ty : template) =
  match e with
  | None, _ -> failwith "bad exp"
  | Some e, _ -> check' env e ty
and check' env e ty = match e with
  | e ->
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
  | Tuple t -> asdf
  | _ -> assert false

and infer_lit = function
  | l, _ -> infer_lit' l
and infer_lit' = function
  | Int _ -> cons_typ Pos Int
  | String _ -> cons_typ Pos String
  
