open Types

module SMap = Map.Make (struct type t = int let compare = compare end)

type scheme = 
  { environment : state SMap.t;
    expr : state }

type typing =
    scheme SMap.t -> scheme

let clone_scheme s =
  Types.clone (fun f -> { environment = SMap.map f s.environment; expr = f s.expr })
    
let constrain (inputs : (state * var typeterm) list) p output =
  let (inputs, output) = compile_terms (fun f ->
    (List.map (fun (s, t) -> (s, f (polneg s.Types.State.pol) t)) inputs, f p output)) in
  if not (List.fold_left (fun b (s, c) -> b && 
    match s.Types.State.pol with
    | Pos -> assert (c.Types.State.pol = Neg); contraction s c
    | Neg -> assert (c.Types.State.pol = Pos); contraction c s) true inputs)
  then failwith "type error of some sort";
  output

let ascription scheme typeterm =
  let s = compile_terms (fun f -> f Pos typeterm) in
  let top = compile_terms (fun f -> f Neg ty_zero) in
  match subsumed (fun f -> f scheme.expr s &&
                             SMap.for_all (fun v sv -> f sv top) scheme.environment) with
  | false -> failwith "ascription check failed"
  | true -> { environment = SMap.empty; expr = s }

let env_join = SMap.merge (fun k a b -> match a, b with
  | (None, x) | (x, None) -> x
  | Some a, Some b ->
    Some (constrain [a, TVar "a"; b, TVar "a"] Neg (TVar "a")))

open Exp
let rec typecheck gamma = function
  | Var v ->
     clone_scheme (SMap.find v gamma)
                  
  | Lambda (arg, body) ->
     let singleton = compile_terms (fun f -> {
          environment = SMap.singleton arg (f Neg (TVar "a"));
          expr = f Pos (TVar "a")}) in
     let body_ty = typecheck (SMap.add arg singleton gamma) body in
     let var = try [SMap.find arg body_ty.environment, TVar "a"] with Not_found -> [] in
      { environment = SMap.remove arg body_ty.environment;
        expr = constrain ((body_ty.expr, TVar "b") :: var) Pos (ty_fun (TVar "a") (TVar "b")) }

  | Let (name, exp, body) ->
     let exp_ty = typecheck gamma exp in
     let body_ty = typecheck (SMap.add name exp_ty gamma) body in
     (* CBV soundness: use exp_ty even if name is unused *)
     { environment = env_join exp_ty.environment body_ty.environment;
       expr = body_ty.expr }

  | App (fn, arg) ->
     let fn_ty = typecheck gamma fn and arg_ty = typecheck gamma arg in
     { environment = env_join fn_ty.environment arg_ty.environment;
       expr = constrain [fn_ty.expr, ty_fun (TVar "a") (TVar "b");
                         arg_ty.expr, TVar "a"] Pos (TVar "b") }

  | Ascription (e, ty) ->
     ascription (typecheck gamma e) ty
       
  | Unit -> 
     { environment = SMap.empty; expr = constrain [] Pos (ty_unit ()) }

  | Object o ->
     let (env, fields) = List.fold_right (fun (s, e) (env, fields) ->
        let {environment = env'; expr = expr'} = typecheck gamma e in
        (env_join env env', (s, expr') :: fields)) o (SMap.empty, []) in
     let constraints = List.map (fun (sym, ty) -> 
        (ty, TVar (Symbol.to_string sym))) fields in
     let o = List.fold_right (fun (sym, ty) o ->
        Types.SMap.add sym (TVar (Symbol.to_string sym)) o) fields Types.SMap.empty in
     { environment = env; expr = constrain constraints Pos (ty_obj o) }

  | GetField (e, field) ->
     let e_ty = typecheck gamma e in
     { environment = e_ty.environment;
       expr = constrain [e_ty.expr,
                         ty_obj (Types.SMap.singleton field (TVar "a"))]
                        Pos (TVar "a") }
