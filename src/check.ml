(*
open Exp
open Typedefs
open Types
let env0_ext =
  Etype (StrMap.of_seq (List.to_seq [
      "any", (tcons Annih, tcons Ident);
      "nothing", (tcons Ident, tcons Annih)]))

let env0 =
  env_cons Env_empty env0_ext

let head_any = Abs ("any", Free env0)
let head_nothing = Abs ("nothing", Free env0)

module Env = struct
  let rec lookup_type env s =
    match env with
    | Env_empty ->
       None
    | Env_cons { entry = Etype tys; rest; _ }
         when StrMap.mem s.label tys ->
       if s.shift = 0 then
         Some env
       else
         lookup_type rest {s with shift = s.shift - 1}
    | Env_cons { rest; _ } ->
       lookup_type rest s
end

let rec typ_of_tyexp env pol = function
  | None, _ -> failwith "bad type"
  | Some t, _ -> typ_of_tyexp' env pol t
and typ_of_tyexp' env pol : tyexp' -> typ = function
  | Tnamed (s, _) ->
     (match Env.lookup_type env s with
      | None ->
         failwith "unknown ctor"
      | Some env ->
         Tcons (IntMap.empty, Abs (s.label, Free env)))
  | Tforall (vars, body) ->
     let vars = vars |> List.fold_left (fun vars ((s,_), l, u) ->
       let l =
         match l with
         | None -> cons Ident
         | Some l ->
            try_styp_of_typ (typ_of_tyexp env_ pol l) in
       let u =
         match u with
         | None -> cons Ident
         | Some u ->
            try_styp_of_typ (typ_of_tyexp env_ (polneg pol) u) in
       if StrMap.mem s vars then
         failwith "duplicate bound variable s";
       StrMap.add s (l, u) vars) StrMap.empty in
     let body = typ_of_tyexp env_ pol body in
     Tforall (vars, body)
  | Trecord (fields, `Closed) ->
     tcons (Record (typs_of_tuple_tyexp env pol fields))
  | Tfunc (args, res) ->
     tcons (Func (typs_of_tuple_tyexp env (polneg pol) args,
                  typ_of_tyexp env pol res))
  | Tparen t ->
     typ_of_tyexp env pol t
  | Tjoin (s, t) ->
     assert false
  | Tmeet (s, t) ->
     assert false

and typs_of_tuple_tyexp env pol = function
  | None, _ -> failwith "bad tuple of types"
  | Some t, _ -> typs_of_tuple_tyexp' env pol t
and typs_of_tuple_tyexp' env pol t =
  let posid = ref 0 in
  t |> List.fold_left (fun fields f ->
    let s, d = match f with
      | TFpositional d ->
         let r = "$" ^ string_of_int !posid in
         incr posid;
         (r, d)
      | TFnamed ((s,_), d) ->
         (s, d) in
    if StrMap.mem s fields then
      failwith ("duplicate field names " ^ s);
    StrMap.add s (typ_of_tyexp env pol d) fields
  ) StrMap.empty

(*
let tyexp_of_typ env pol : typ -> tyexp = function
  | Tcons (vars, cons) ->
     let cons = match cons with
       | Ident ->
          (match pol with Pos -> head_nothing | Neg -> head_any)
       | Annih ->
          (match pol with Pos -> head_any | Neg -> head_nothing)
       | Record fields ->
          StrMap.fold



 *)
let infer env = assert false
 *)
