open Exp
open Typedefs
open Types

module Env = struct
  let rec lookup_type env s =
    match env with
    | Env_empty ->
       None
    | Env_cons { entry = EType (s', _, _); _ } when s = s' ->
       Some env
    | Env_cons { rest; _ } ->
       lookup_type rest s
end

let rec typ_of_tyexp env = function
  | None, _ -> failwith "bad type"
  | Some t, _ -> typ_of_tyexp' env t
and typ_of_tyexp' env pol = function
  (* FIXME: better names for top/bot *)
  | Tnamed ("any", _) ->
     Tcons (IntMap.empty, match pol with Pos -> Annih | Neg -> Ident)
  | Tnamed ("nothing", _) ->
     Tcons (IntMap.empty, match pol with Pos -> Ident | Neg -> Annih)
  | Tnamed (s, _) ->
     (match Env.lookup_type env s with
      | None ->
         failwith "unknown ctor"
      | Some env ->
         Tcons (IntMap.empty, Abs (s, env)))
  | _ -> assert false     


let infer env = assert false
