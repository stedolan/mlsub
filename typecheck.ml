open Types

module SMap = Map.Make (struct type t = int let compare = compare end)

type scheme = 
  { environment : state SMap.t;
    expr : state }

type typing =
    scheme SMap.t -> scheme

let clone_scheme s =
  Types.clone (fun f -> { environment = SMap.map f s.environment; expr = f s.expr })
    
let constrain name (inputs : (state * var typeterm) list) p output =
  let (inputs, output) = compile_terms (fun f ->
    (List.map (fun (s, t) -> (s, f (polneg s.Types.State.pol) t)) inputs, f p output)) in
  let dump title =
    let find_states f =
      let id = ref 0 in
      List.iter (fun (s, t) ->
                 f (Printf.sprintf "s-%d" !id) s;
                 f (Printf.sprintf "t-%d" !id) t;
                 incr id) inputs;
      f "out" output in
    Format.printf "%a\n%!" (print_automaton title) find_states in
  let debug = false in
  if debug then dump (name ^ "_before");
  if not (List.fold_left (fun b (s, c) -> b && 
    match s.Types.State.pol with
    | Pos -> assert (c.Types.State.pol = Neg); contraction s c
    | Neg -> assert (c.Types.State.pol = Pos); contraction c s) true inputs)
  then failwith "type error of some sort";
  if debug then dump (name ^ "_after");
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
    Some (constrain "join" [a, TVar "a"; b, TVar "a"] Neg (TVar "a")))

let add_singleton v gamma =
  let singleton = compile_terms (fun f -> {
        environment = SMap.singleton v (f Neg (TVar "a"));
        expr = f Pos (TVar "a")}) in
  SMap.add v singleton gamma


open Exp
let rec typecheck gamma (loc, exp) = match exp with
  | Var v ->
     (try clone_scheme (SMap.find v gamma)
      with Not_found -> failwith ("unbound variable '" ^ Symbol.to_string v ^ "'"))
                  
  | Lambda (arg, body) ->
     let body_ty = typecheck (add_singleton arg gamma) body in
     let var = try [SMap.find arg body_ty.environment, TVar "a"] with Not_found -> [] in
      { environment = SMap.remove arg body_ty.environment;
        expr = constrain "lambda" ((body_ty.expr, TVar "b") :: var) Pos (ty_fun (TVar "a") (TVar "b")) }

  | Let (name, exp, body) ->
     let exp_ty = typecheck gamma exp in
     let body_ty = typecheck (SMap.add name exp_ty gamma) body in
     (* CBV soundness: use exp_ty even if name is unused *)
     { environment = env_join exp_ty.environment body_ty.environment;
       expr = body_ty.expr }

  | Rec (v, exp) ->
     let exp_ty = typecheck (add_singleton v gamma) exp in
     let var = try [SMap.find v exp_ty.environment, TVar "a"] with Not_found -> [] in
     { environment = SMap.remove v exp_ty.environment;
       expr = constrain "rec" ((exp_ty.expr, TVar "a") :: var) Pos (TVar "a") }

  | App (fn, arg) ->
     let fn_ty = typecheck gamma fn and arg_ty = typecheck gamma arg in
     { environment = env_join fn_ty.environment arg_ty.environment;
       expr = constrain "app" [fn_ty.expr, ty_fun (TVar "a") (TVar "b");
                               arg_ty.expr, TVar "a"] Pos (TVar "b") }

  | Ascription (e, ty) ->
     ascription (typecheck gamma e) ty
       
  | Unit -> 
     { environment = SMap.empty; expr = constrain "unit" [] Pos (ty_base (Symbol.intern "unit")) }

  | Int n ->
     { environment = SMap.empty; expr = constrain "int" [] Pos (ty_base (Symbol.intern "int")) }

  | Bool b ->
     { environment = SMap.empty; expr = constrain "bool" [] Pos (ty_base (Symbol.intern "bool")) }

  | If (cond, tcase, fcase) ->
     let {environment = envC; expr = exprC} = typecheck gamma cond in
     let {environment = envT; expr = exprT} = typecheck gamma tcase in
     let {environment = envF; expr = exprF} = typecheck gamma fcase in
     { environment = env_join envC (env_join envT envF);
       expr = constrain "if" [exprC, ty_base (Symbol.intern "bool");
                              exprT, TVar "a";
                              exprF, TVar "a"] Pos (TVar "a") }
  | Nil ->
     { environment = SMap.empty; expr = constrain "nil" [] Pos (ty_list (TVar "a")) }
  | Cons (x, xs) ->
     let x_ty = typecheck gamma x in
     let xs_ty = typecheck gamma xs in
     { environment = env_join x_ty.environment xs_ty.environment;
       expr = constrain "cons" [x_ty.expr, TVar "a";
                                xs_ty.expr, ty_list (TVar "a")] Pos (ty_list (TVar "a")) }
  | Match (e, nil, x, xs, cons) ->
     let e_ty = typecheck gamma e in
     let nil_ty = typecheck gamma nil in
     let cons_ty = typecheck (add_singleton x (add_singleton xs gamma)) cons in
     let vars =
       (try [SMap.find x cons_ty.environment, TVar "a"] with Not_found -> []) @
       (try [SMap.find xs cons_ty.environment, ty_list (TVar "a")] with Not_found -> []) in
     { environment = env_join e_ty.environment (env_join nil_ty.environment (SMap.remove x (SMap.remove xs cons_ty.environment)));
       expr = constrain "match" ([e_ty.expr, ty_list (TVar "a");
                                  nil_ty.expr, TVar "res";
                                  cons_ty.expr, TVar "res"]
                                 @ vars) Pos (TVar "res") }

  | Object o ->
     let (env, fields) = List.fold_right (fun (s, e) (env, fields) ->
        let {environment = env'; expr = expr'} = typecheck gamma e in
        (env_join env env', (s, expr') :: fields)) o (SMap.empty, []) in
     let constraints = List.map (fun (sym, ty) -> 
        (ty, TVar (Symbol.to_string sym))) fields in
     let o = List.fold_right (fun (sym, ty) o ->
        Types.SMap.add sym (TVar (Symbol.to_string sym)) o) fields Types.SMap.empty in
     { environment = env; expr = constrain "object" constraints Pos (ty_obj o) }

  | GetField (e, field) ->
     let e_ty = typecheck gamma e in
     { environment = e_ty.environment;
       expr = constrain "field" [e_ty.expr,
                                 ty_obj (Types.SMap.singleton field (TVar "a"))]
                        Pos (TVar "a") }


let ty_int = ty_base (Symbol.intern "int")
let ty_unit = ty_base (Symbol.intern "unit")
let ty_bool = ty_base (Symbol.intern "bool")

let ty_fun2 x y res = ty_fun x (ty_fun y res)

let ty_polycmp = ty_fun2 (TVar "a") (TVar "a") ty_bool
let ty_binarith = ty_fun2 ty_int ty_int ty_int

let predefined =
  ["p", ty_fun ty_int ty_unit;
   "error", ty_fun ty_unit ty_zero;
   "(=)", ty_polycmp;
   "(==)", ty_polycmp;
   "(<)", ty_polycmp;
   "(>)", ty_polycmp;
   "(<=)", ty_polycmp;
   "(>=)", ty_polycmp;
   "(+)", ty_binarith;
   "(-)", ty_binarith
  ]

let gamma0 =
  List.fold_right
    (fun (n, t) g ->
     SMap.add (Symbol.intern n)
              { environment = SMap.empty;
                expr = (compile_terms (fun f -> f Pos t)) } g)
    predefined SMap.empty


let optimise s =
  let states = s.expr :: SMap.fold (fun v s ss -> s :: ss) s.environment [] in
  Types.optimise_flow states;
  s
       
type result =
  | Type of scheme
  | TypeError of string



let infer_module modlist =
  let recomp s =
    assert (s.environment = SMap.empty);
    { environment = SMap.empty; expr = compile_terms (fun f -> f Pos (decompile_automaton s.expr)) } in 
  let infer gamma exp =
    try
      let s = typecheck gamma exp in
      Type (recomp (optimise s))
    with
    | Failure msg -> TypeError ("Type inference failed: " ^ msg)
    | Match_failure (file, line, col) ->
       TypeError (Format.sprintf "Match failure in typechecker at %s:%d%d\n%!" file line col) in

  let rec infer_mod gamma acc = function
    | [] -> acc
    | (name, exp) :: rest ->
       let t = infer gamma exp in
       match t with
       | Type s -> infer_mod (SMap.add (Symbol.intern name) s gamma) ((name, t) :: acc) rest
       | TypeError _ -> (name, t) :: acc in
  
  List.rev (infer_mod gamma0 [] modlist)

