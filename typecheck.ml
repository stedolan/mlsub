open Variance
open Typector
open Types
open Exp

module SMap = Map.Make (struct type t = int let compare = compare end)

type scheme = 
  { environment : state SMap.t;
    expr : state }

type dscheme =
  { d_environment : dstate SMap.t;
    d_expr : dstate }

type typing =
    scheme SMap.t -> scheme

let to_dscheme s =
  let states = s.expr :: SMap.fold (fun v s ss -> s :: ss) s.environment [] in
  let remap, dstates = Types.determinise states in
  let minim = Types.minimise dstates in
  let remap x = minim (remap x) in 
  { d_environment = SMap.map remap s.environment; d_expr = remap s.expr }

let clone_scheme loc s =
  Types.clone (fun f -> { environment = SMap.map (f loc) s.d_environment; expr = f loc s.d_expr })

let constrain' ctx err p n =
  let success = ref true in
  List.iter (fun e -> success := false; err e) (Types.constrain p n);
  !success

let dump_scheme title {environment; expr} =
  Format.printf "%a\n%!" (print_automaton title) (fun f ->
    f "out" expr;
    SMap.iter (fun n s -> f (Symbol.to_string n) s) environment)

let constrain ctx err name (inputs : (state * state) list) output =
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
  let errs = (List.fold_left (fun rs (p, n) -> rs @ constrain p n) [] inputs) in
  List.iter err errs;
  if debug then dump (name ^ "_after");
  match errs with
  | [] -> output
  | _ :: _ -> compile_type ctx Pos (TZero Pos)

let ty_join ctx err a b =
  let (jN, jP) = Types.flow_pair () in
  constrain ctx err "join" [a, jN; b, jN] jP

let ascription ctx scheme typeterm =
  let s = compile_type ctx Pos typeterm in
  let top = compile_type ctx Neg (TZero Neg) in
  let dsch = to_dscheme { environment = SMap.map (fun _ -> top) scheme.environment; expr = s } in
  match subsumed (fun f -> f Pos scheme.expr dsch.d_expr &&
                             SMap.for_all (fun v sv -> 
                               f Neg sv (SMap.find v dsch.d_environment)) scheme.environment) with
  | false -> failwith "ascription check failed"
  | true -> { environment = SMap.empty; expr = s }

let env_join err loc = SMap.merge (fun k a b -> match a, b with
  | (None, x) | (x, None) -> x
  | Some a, Some b ->
     let (jN, jP) = Types.flow_pair () in
     Some (constrain Types.empty_context err "join" [jP, a; jP, b] jN))
(* Some (Types.join a b)) *) 

let add_singleton v gamma loc =
  let (n, p) = Types.flow_pair () in
  let singleton = {
    environment = SMap.singleton v n;
    expr = p} in
  SMap.add v (to_dscheme singleton) gamma


open Exp
let var env arg t = try [t, SMap.find arg env] with Not_found -> []

let failure ctx err e loc =
  err e;
  { environment = SMap.empty; expr = compile_type ctx Pos (TZero Pos) }

let ty_int = ty_base (Symbol.intern "int")
let ty_unit = ty_base (Symbol.intern "unit")
let ty_bool = ty_base (Symbol.intern "bool")


let rec typecheck ctx err gamma = function
| (loc, Some exp) -> typecheck' ctx err gamma loc exp
| (loc, None) -> failure ctx err (Error.SyntaxErr loc) loc
and typecheck' ctx err gamma loc exp = match exp with
  | Var v ->
     (try clone_scheme (Location.one loc) (SMap.find v gamma)
      with Not_found -> failure ctx err (Error.Unbound (loc, v)) loc)

  | Lambda (params, body) ->
     let rec check_params gamma = function
       (* FIXME check for duplicate arguments *)
       (* FIXME check type parameters and type annotations *)
       | [] -> typecheck ctx err gamma body
       | (loc, (((Ppositional arg | Preq_keyword arg | Popt_keyword(arg, _)) as param), asc)) :: params ->
          let gamma = match asc with
            | Some t -> SMap.add arg (to_dscheme {
              environment = SMap.singleton arg (compile_type ctx Neg t);
              expr = compile_type ctx Pos t}) gamma
            | None -> add_singleton arg gamma loc in
          let body_ty = check_params gamma params in
          let env = match param with
            | Popt_keyword (arg, default) ->
               let {environment = envD; expr = exprD} = typecheck ctx err gamma default in
               let (defaultN, defaultP) = Types.flow_pair () in
               let _ = constrain' ctx err exprD defaultN in
               (match SMap.find arg body_ty.environment with
                | t -> let _ = constrain' ctx err defaultP t in ()
                | exception Not_found -> ());
               env_join err loc envD body_ty.environment
            | _ -> body_ty.environment in
          { environment = env; expr = body_ty.expr } in

     let rec build_funtype env expr pos kwargs = function
       | [] -> { environment = env;
                 expr = Types.cons Pos (ty_fun (List.rev pos) kwargs expr loc) }
       | (loc, (((Ppositional arg | Preq_keyword arg | Popt_keyword (arg, _)) as param), _)) :: params ->
          let argty = try SMap.find arg env with Not_found -> Types.zero Neg in
          let env = SMap.remove arg env in
          let argty = fun _ -> argty in (* FIXME *)
          match param with
          | Ppositional _ -> 
             build_funtype env expr (argty :: pos) kwargs params
          | Preq_keyword arg -> 
             build_funtype env expr pos (Typector.SMap.add arg (argty, true) kwargs) params
          | Popt_keyword (arg, _) -> 
             build_funtype env expr pos (Typector.SMap.add arg (argty, false) kwargs) params in

     let { environment; expr } = check_params gamma params in
     build_funtype environment (fun _ -> expr) [] (Typector.SMap.empty) params
(*
     let body_ty = check_params gamma params in
     let argvar k = ty_var ("arg-" ^ Symbol.to_string k) in
     let rec remove_params env = function
       | [] -> [], env
       | (loc, ((Ppositional arg | Preq_keyword arg | Popt_keyword (arg, _)), ty)) :: params ->
          let (constraints, env) = remove_params env params in
          let constraints = match ty with
            | None -> constraints
            | Some ty ->
               (* FIXME default arg unchecked here *)
               match SMap.find arg env with
               | v -> Printf.printf "constraining\n%!"; (v, ty) :: constraints
               | exception Not_found -> constraints in 
          (var env arg (argvar arg loc) @ constraints), SMap.remove arg env in
     let rec build_funtype pos kwargs = function
       | [] -> ty_fun (List.rev pos) kwargs (ty_var "res") loc
       | (loc, (Ppositional arg, _)) :: params ->
          build_funtype (argvar arg :: pos) kwargs params
       | (loc, (Preq_keyword arg, _)) :: params ->
          build_funtype pos (Typector.SMap.add arg (argvar arg, true) kwargs) params
       | (loc, (Popt_keyword (arg, _), _)) :: params ->
          build_funtype pos (Typector.SMap.add arg (argvar arg, false) kwargs) params in
     let (constraints, env) = remove_params body_ty.environment params in
     { environment = env;
       expr = constrain err "lambda" ((body_ty.expr, ty_var "res" loc) :: constraints) Pos (TCons (build_funtype [] Typector.SMap.empty params)) }
*)
  | Let (name, exp, body) ->
     let exp_ty = typecheck ctx err gamma exp in
     let body_ty = typecheck ctx err (SMap.add name (to_dscheme exp_ty) gamma) body in
     (* CBV soundness: use exp_ty even if name is unused *)
     { environment = env_join err loc exp_ty.environment body_ty.environment;
       expr = body_ty.expr }

  | Rec (v, exp) ->
     let exp_ty = typecheck ctx err (add_singleton v gamma loc) exp in
     let (recN, recP) = Types.flow_pair () in
     let var = try [recP, SMap.find v exp_ty.environment] with Not_found -> [] in
     { environment = SMap.remove v exp_ty.environment;
       expr = constrain ctx err "rec" ((exp_ty.expr, recN) :: var) recP }

  | App (fn, args) ->
     let { environment = envF; expr = exprF } = typecheck ctx err gamma fn in
     let rec check_args env pos kwargs constraints = function
       | [] ->
          let (resN, resP) = Types.flow_pair () in
          { environment = env;
            expr = constrain ctx err "app" 
              ((exprF, Types.cons Neg (ty_fun (List.rev pos) kwargs (fun _ -> resN) loc))
               :: constraints) 
              resP }
       | (loc, Apositional e) :: args ->
          let { environment = envE; expr = exprE } = typecheck ctx err gamma e in
          let (argN, argP) = Types.flow_pair () in
          check_args (env_join err loc env envE) ((fun _ -> argP) :: pos) kwargs ((exprE, argN) :: constraints) args
       | (loc, Akeyword (k, e)) :: args ->
          let { environment = envE; expr = exprE } = typecheck ctx err gamma e in
          let (argN, argP) = Types.flow_pair () in
          check_args (env_join err loc env envE) pos (Typector.SMap.add k ((fun _ -> argP), true) kwargs) ((exprE, argN) :: constraints) args in
     check_args envF [] Typector.SMap.empty [] args

  | Seq (e1, e2) ->
     let {environment = env1; expr = expr1 } = typecheck ctx err gamma e1 in
     let {environment = env2; expr = expr2 } = typecheck ctx err gamma e2 in
     let (expN, expP) = Types.flow_pair () in
     { environment = env_join err loc env1 env2;
       expr = constrain ctx err "seq" [(expr1, Types.cons Neg (ty_unit loc)); (expr2, expN)] expP }

  | Typed (e, ty) ->
     (* FIXME *)
     (* ascription (typecheck err gamma e) ty *)
     typecheck ctx err gamma e

  | Unit -> 
     { environment = SMap.empty; expr = Types.cons Pos (ty_base (Symbol.intern "unit") loc) }

  | Int n ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_base (Symbol.intern "int") loc) }

  | Bool b ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_base (Symbol.intern "bool") loc) }

  | If (cond, tcase, fcase) ->
     let {environment = envC; expr = exprC} = typecheck ctx err gamma cond in
     let {environment = envT; expr = exprT} = typecheck ctx err gamma tcase in
     let {environment = envF; expr = exprF} = typecheck ctx err gamma fcase in
     { environment = env_join err loc envC (env_join err loc envT envF);
       expr = constrain ctx err "if" [exprC, Types.cons Neg (ty_base (Symbol.intern "bool") loc)]
         (ty_join ctx err exprT exprF) }
  | Nil ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_list (fun _ -> Types.zero Pos) loc) }
  | Cons (x, xs) ->
     let x_ty = typecheck ctx err gamma x in
     let xs_ty = typecheck ctx err gamma xs in
     let (xN, xP) = Types.flow_pair () and (xsN, xsP) = Types.flow_pair () in
     { environment = env_join err loc x_ty.environment xs_ty.environment;
       expr = constrain ctx err "cons" [x_ty.expr, xN;
                                xs_ty.expr, Types.cons Neg (ty_list (fun _ -> xsN) loc)] (Types.cons Pos (ty_list (fun _ -> ty_join ctx err xP xsP) loc)) }
  | Match (e, nil, x, xs, cons) ->
     let e_ty = typecheck ctx err gamma e in
     let nil_ty = typecheck ctx err gamma nil in
     let cons_ty = typecheck ctx err (add_singleton x (add_singleton xs gamma loc) loc) cons in
     let (xN, xP) = Types.flow_pair () in
     let vars =
       (try [xP, SMap.find x cons_ty.environment] with Not_found -> []) @
       (try [Types.cons Pos (ty_list (fun _ -> xP) loc), SMap.find xs cons_ty.environment] with Not_found -> []) in
     { environment = env_join err loc e_ty.environment (env_join err loc nil_ty.environment (SMap.remove x (SMap.remove xs cons_ty.environment)));
       expr = constrain ctx err "match" ([e_ty.expr, Types.cons Neg (ty_list (fun _ -> xN) loc)] @ vars)
         (ty_join ctx err nil_ty.expr cons_ty.expr) }

  | Object o ->
     let (env, fields) = List.fold_right (fun (s, e) (env, fields) ->
        let {environment = env'; expr = expr'} = typecheck ctx err gamma e in
        if Typector.SMap.mem s fields then failwith "Duplicate field";
        (env_join err loc env env', Typector.SMap.add s (fun _ -> expr') fields)) o (SMap.empty, Typector.SMap.empty) in
     { environment = env; expr = Types.cons Pos (ty_obj fields loc) }

  | GetField (e, field) ->
     let e_ty = typecheck ctx err gamma e in
     let (xN, xP) = Types.flow_pair () in
     { environment = e_ty.environment;
       expr = constrain ctx err "field" [e_ty.expr,
                                     Types.cons Neg (ty_obj (Typector.SMap.singleton field (fun _ -> xN)) loc)]
                        xP }


let ty_cons t loc = TCons (t loc)
let ty_fun2 x y res = ty_fun [x; y] Typector.SMap.empty res

let ty_polycmp = ty_fun2 (fun _ -> TZero Neg) (fun _ -> TZero Neg) (ty_cons (ty_bool))
let ty_binarith = ty_fun2 (ty_cons ty_int) (ty_cons ty_int) (ty_cons ty_int)

let predefined =
  ["p", ty_fun [ty_cons ty_int] Typector.SMap.empty (ty_cons ty_unit);
   "error", ty_fun [ty_cons ty_unit] Typector.SMap.empty (fun loc -> TZero Pos);
   "(==)", ty_polycmp;
   "(<)", ty_polycmp;
   "(>)", ty_polycmp;
   "(<=)", ty_polycmp;
   "(>=)", ty_polycmp;
   "(+)", ty_binarith;
   "(-)", ty_binarith] 
  |> List.map (fun (n, t) -> (n, ty_cons t Location.internal))

let ctx0 =
  Types.empty_context
  |> Types.add_opaque_type () (Symbol.intern "int") []

let gamma0 =
  List.fold_right
    (fun (n, t) g ->
     SMap.add (Symbol.intern n)
              (to_dscheme { environment = SMap.empty;
                            expr = compile_type ctx0 Pos t }) g)
    predefined SMap.empty

type result =
  | Type of scheme
  | TypeError of string


type 'a sigitem =
  | SDef of Symbol.t * 'a
  | SLet of Symbol.t * 'a
and signature = dstate sigitem list

let rec infer_module err modl : signature =
  let rec infer tyctx gamma = function
    | [] -> SMap.empty, []
    | (loc, MType (t, p, body)) :: modl ->
       (* Type definition *)
       infer (Types.add_type_alias err t p body tyctx) gamma modl
    | (loc, MDef (f, p, body)) :: modl ->
       (* Possibly-recursive function *)
       let {environment = envF; expr = exprF} as tyF =
         typecheck' tyctx err gamma loc (Rec (f, (loc, Some (Lambda (p, body))))) in
       let envM, sigM = infer tyctx (SMap.add f (to_dscheme tyF) gamma) modl in
       env_join err loc envF envM, (SDef (f, exprF) :: sigM)
    | (loc, MLet (v, e)) :: modl ->
       let {environment = envE; expr = exprE} = typecheck tyctx err gamma e in
       let envM, sigM = infer tyctx (add_singleton v gamma loc) modl in
       env_join err loc envE (SMap.remove v envM),
       let (expN, expP) = Types.flow_pair () in
       (SLet (v, constrain tyctx err "let" ((exprE, expN) :: var envM v expP)
         expP) :: sigM) in
  let envM, sigM = infer ctx0 gamma0 modl in
  assert (SMap.is_empty envM);
  let states = List.map (function SDef (f, t) -> t | SLet (v, t) -> t) sigM in
  let remap, dstates = Types.determinise states in
  Types.optimise_flow dstates;
  let minim = Types.minimise dstates in
  List.map (function SDef (f, t) -> SDef (f, minim (remap t)) | SLet (v, t) -> SLet (v, minim (remap t))) sigM

let rec print_signature ppf (sigm : signature) =
  let elems = sigm
     |> Types.clone (fun f -> List.map (function SLet (_, t) | SDef (_, t) -> f (Location.one Location.internal) t))
     |> decompile_automaton in
  let print s t = match s with
    | SLet (v, _) ->
       Format.fprintf ppf "val %s : %a\n%!" (Symbol.to_string v) print_typeterm t
    | SDef (f, _) ->
       Format.fprintf ppf "def %s : %a\n%!" (Symbol.to_string f) print_typeterm t in
  List.iter2 print sigm elems
