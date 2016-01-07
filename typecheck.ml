open Types

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
    
let constrain err name (inputs : (state * var typeterm) list) p output =
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
    Format.printf "%a\n%!" (print_automaton title (fun s -> s.Types.State.id)) find_states in
  let debug = false in
  if debug then dump (name ^ "_before");
  let errs = (List.fold_left (fun rs (s, c) -> rs @
    match s.Types.State.pol with
    | Pos -> assert (c.Types.State.pol = Neg); contraction s c
    | Neg -> assert (c.Types.State.pol = Pos); contraction c s) [] inputs) in
  List.iter err errs;
  if debug then dump (name ^ "_after");
  match errs with
  | [] -> output
  | _ :: _ -> compile_terms (fun f -> f Pos (ty_var "a" Location.internal)) (* FIXME not internal *)

let ascription scheme typeterm =
  let s = compile_terms (fun f -> f Pos typeterm) in
  let top = compile_terms (fun f -> f Neg (ty_zero Location.internal)) in
  let dsch = to_dscheme { environment = SMap.map (fun _ -> top) scheme.environment; expr = s } in
  match subsumed (fun f -> f Pos scheme.expr dsch.d_expr &&
                             SMap.for_all (fun v sv -> 
                               f Neg sv (SMap.find v dsch.d_environment)) scheme.environment) with
  | false -> failwith "ascription check failed"
  | true -> { environment = SMap.empty; expr = s }

let env_join err loc = SMap.merge (fun k a b -> match a, b with
  | (None, x) | (x, None) -> x
  | Some a, Some b ->
    Some (constrain err "join" [a, ty_var "a" loc; b, ty_var "a" loc] Neg (ty_var "a" loc)))

let add_singleton v gamma loc =
  let singleton = compile_terms (fun f -> {
        environment = SMap.singleton v (f Neg (ty_var "a" loc));
        expr = f Pos (ty_var "a" loc)}) in
  SMap.add v (to_dscheme singleton) gamma


open Exp
let var env arg t = try [SMap.find arg env, t] with Not_found -> []
let bottom loc = compile_terms (fun f -> { environment = SMap.empty; expr = f Pos (ty_zero loc) })


let ty_int = ty_base (Symbol.intern "int")
let ty_unit = ty_base (Symbol.intern "unit")
let ty_bool = ty_base (Symbol.intern "bool")


let rec typecheck err gamma = function
| (loc, Some exp) -> typecheck' err gamma loc exp
| (loc, None) -> (err (Reason.SyntaxErr loc); bottom loc)
and typecheck' err gamma loc exp = match exp with
  | Var v ->
     (try clone_scheme (Location.one loc) (SMap.find v gamma)
      with Not_found -> (err (Reason.Unbound (loc, v)); bottom loc))
                  
  | Lambda (params, body) ->
     let rec check_params gamma = function
       (* FIXME check for duplicate arguments *)
       | [] -> typecheck err gamma body
       | (loc, (Ppositional arg | Preq_keyword arg)) :: params -> check_params (add_singleton arg gamma loc) params
       | (loc, Popt_keyword(arg, default)) :: params ->
          let {environment = envD; expr = exprD} = typecheck err gamma default in
          let {environment = envE; expr = exprE} = check_params (add_singleton arg gamma loc) params in
          { environment = env_join err loc envD envE;
            expr = constrain err "default-arg" ([(exprE, ty_var "a" loc); (exprD, ty_var "d" loc)] @ var envE arg (ty_var "d" loc))
              Pos (ty_var "a" loc) } in
     let body_ty = check_params gamma params in
     let argvar k = ty_var ("arg-" ^ Symbol.to_string k) in
     let rec remove_params env = function
       | [] -> [], env
       | (loc, (Ppositional arg | Preq_keyword arg | Popt_keyword (arg, _))) :: params ->
          let (constraints, env) = remove_params env params in
          (var env arg (argvar arg loc) @ constraints), SMap.remove arg env in
     let rec build_funtype pos kwargs = function
       | [] -> ty_fun (List.rev pos) kwargs (ty_var "res") loc
       | (loc, Ppositional arg) :: params ->
          build_funtype (argvar arg :: pos) kwargs params
       | (loc, Preq_keyword arg) :: params ->
          build_funtype pos (Types.SMap.add arg (argvar arg, true) kwargs) params
       | (loc, Popt_keyword (arg, _)) :: params ->
          build_funtype pos (Types.SMap.add arg (argvar arg, false) kwargs) params in
     let (constraints, env) = remove_params body_ty.environment params in
     { environment = env;
       expr = constrain err "lambda" ((body_ty.expr, ty_var "res" loc) :: constraints) Pos (build_funtype [] Types.SMap.empty params) }

  | Let (name, exp, body) ->
     let exp_ty = typecheck err gamma exp in
     let body_ty = typecheck err (SMap.add name (to_dscheme exp_ty) gamma) body in
     (* CBV soundness: use exp_ty even if name is unused *)
     { environment = env_join err loc exp_ty.environment body_ty.environment;
       expr = body_ty.expr }

  | Rec (v, exp) ->
     let exp_ty = typecheck err (add_singleton v gamma loc) exp in
     let var = try [SMap.find v exp_ty.environment, ty_var "a" loc] with Not_found -> [] in
     { environment = SMap.remove v exp_ty.environment;
       expr = constrain err "rec" ((exp_ty.expr, ty_var "a" loc) :: var) Pos (ty_var "a" loc) }

  | App (fn, args) ->
     let { environment = envF; expr = exprF } = typecheck err gamma fn in
     let fresh =
       let id = ref 0 in
       fun () -> incr id; ty_var ("arg-" ^ string_of_int !id) in
     let rec check_args env pos kwargs constraints = function
       | [] ->
          { environment = env;
            expr = constrain err "app" ((exprF, ty_fun (List.rev pos) kwargs (ty_var "res") loc) :: constraints) 
              Pos (ty_var "res" loc) }
       | (loc, Apositional e) :: args ->
          let { environment = envE; expr = exprE } = typecheck err gamma e in
          let var = fresh () in
          check_args (env_join err loc env envE) (var :: pos) kwargs ((exprE, var loc) :: constraints) args
       | (loc, Akeyword (k, e)) :: args ->
          let { environment = envE; expr = exprE } = typecheck err gamma e in
          let var = fresh () in
          check_args (env_join err loc env envE) pos (Types.SMap.add k (var, true) kwargs) ((exprE, var loc) :: constraints) args in
     check_args envF [] Types.SMap.empty [] args
(*               
     let fn_ty = typecheck err gamma fn and arg_ty = typecheck err gamma arg in
     { environment = env_join err loc fn_ty.environment arg_ty.environment;
       expr = constrain err "app" [fn_ty.expr, ty_fun (ty_var "a") (ty_var "b") loc;
                               arg_ty.expr, ty_var "a" loc] Pos (ty_var "b" loc) }
*)

  | Seq (e1, e2) ->
     let {environment = env1; expr = expr1 } = typecheck err gamma e1 in
     let {environment = env2; expr = expr2 } = typecheck err gamma e2 in
     { environment = env_join err loc env1 env2;
       expr = constrain err "seq" [(expr1, ty_unit loc); (expr2, ty_var "a" loc)] Pos (ty_var "a" loc) }

  | Ascription (e, ty) ->
     ascription (typecheck err gamma e) ty
       
  | Unit -> 
     { environment = SMap.empty; expr = constrain err "unit" [] Pos (ty_base (Symbol.intern "unit") loc) }

  | Int n ->
     { environment = SMap.empty; expr = constrain err "int" [] Pos (ty_base (Symbol.intern "int") loc) }

  | Bool b ->
     { environment = SMap.empty; expr = constrain err "bool" [] Pos (ty_base (Symbol.intern "bool") loc) }

  | If (cond, tcase, fcase) ->
     let {environment = envC; expr = exprC} = typecheck err gamma cond in
     let {environment = envT; expr = exprT} = typecheck err gamma tcase in
     let {environment = envF; expr = exprF} = typecheck err gamma fcase in
     { environment = env_join err loc envC (env_join err loc envT envF);
       expr = constrain err "if" [exprC, ty_base (Symbol.intern "bool") loc;
                              exprT, ty_var "a" loc;
                              exprF, ty_var "a" loc] Pos (ty_var "a" loc) }
  | Nil ->
     { environment = SMap.empty; expr = constrain err "nil" [] Pos (ty_list (ty_var "a") loc) }
  | Cons (x, xs) ->
     let x_ty = typecheck err gamma x in
     let xs_ty = typecheck err gamma xs in
     { environment = env_join err loc x_ty.environment xs_ty.environment;
       expr = constrain err "cons" [x_ty.expr, ty_var "a" loc;
                                xs_ty.expr, ty_list (ty_var "a") loc] Pos (ty_list (ty_var "a") loc) }
  | Match (e, nil, x, xs, cons) ->
     let e_ty = typecheck err gamma e in
     let nil_ty = typecheck err gamma nil in
     let cons_ty = typecheck err (add_singleton x (add_singleton xs gamma loc) loc) cons in
     let vars =
       (try [SMap.find x cons_ty.environment, ty_var "a" loc] with Not_found -> []) @
       (try [SMap.find xs cons_ty.environment, ty_list (ty_var "a") loc] with Not_found -> []) in
     { environment = env_join err loc e_ty.environment (env_join err loc nil_ty.environment (SMap.remove x (SMap.remove xs cons_ty.environment)));
       expr = constrain err "match" ([e_ty.expr, ty_list (ty_var "a") loc;
                                  nil_ty.expr, ty_var "res" loc;
                                  cons_ty.expr, ty_var "res" loc]
                                 @ vars) Pos (ty_var "res" loc) }

  | Object o ->
     let (env, fields) = List.fold_right (fun (s, e) (env, fields) ->
        let {environment = env'; expr = expr'} = typecheck err gamma e in
        (env_join err loc env env', (s, expr') :: fields)) o (SMap.empty, []) in
     let constraints = List.map (fun (sym, ty) -> 
        (ty, ty_var (Symbol.to_string sym) loc)) fields in
     let o = List.fold_right (fun (sym, ty) o ->
        Types.SMap.add sym (ty_var (Symbol.to_string sym)) o) fields Types.SMap.empty in
     { environment = env; expr = constrain err "object" constraints Pos (ty_obj o loc) }

  | GetField (e, field) ->
     let e_ty = typecheck err gamma e in
     { environment = e_ty.environment;
       expr = constrain err "field" [e_ty.expr,
                                 ty_obj (Types.SMap.singleton field (ty_var "a")) loc]
                        Pos (ty_var "a" loc) }


let ty_fun2 x y res = ty_fun [x; y] Types.SMap.empty res

let ty_polycmp = ty_fun2 (ty_var "a") (ty_var "a") ty_bool
let ty_binarith = ty_fun2 ty_int ty_int ty_int

let predefined =
  let i = Location.internal in
  ["p", ty_fun [ty_int] Types.SMap.empty ty_unit i;
   "error", ty_fun [ty_unit] Types.SMap.empty ty_zero i;
   "(==)", ty_polycmp i;
   "(<)", ty_polycmp i;
   "(>)", ty_polycmp i;
   "(<=)", ty_polycmp i;
   "(>=)", ty_polycmp i;
   "(+)", ty_binarith i;
   "(-)", ty_binarith i]

let gamma0 =
  List.fold_right
    (fun (n, t) g ->
     SMap.add (Symbol.intern n)
              (to_dscheme { environment = SMap.empty;
                            expr = (compile_terms (fun f -> f Pos t)) }) g)
    predefined SMap.empty

type result =
  | Type of scheme
  | TypeError of string


type 'a sigitem =
  | SDef of Symbol.t * 'a
  | SLet of Symbol.t * 'a
and signature = dstate sigitem list

let rec infer_module err modl : signature =
  let rec infer gamma = function
    | [] -> SMap.empty, []
    | (loc, MDef (f, p, body)) :: modl ->
       (* Possibly-recursive function *)
       let {environment = envF; expr = exprF} as tyF =
         typecheck' err gamma loc (Rec (f, (loc, Some (Lambda (p, body))))) in
       let envM, sigM = infer (SMap.add f (to_dscheme tyF) gamma) modl in
       env_join err loc envF envM, (SDef (f, exprF) :: sigM)
    | (loc, MLet (v, e)) :: modl ->
       let {environment = envE; expr = exprE} = typecheck err gamma e in
       let envM, sigM = infer (add_singleton v gamma loc) modl in
       env_join err loc envE (SMap.remove v envM),
       (SLet (v, constrain err "let" ((exprE, ty_var "a" loc) :: var envM v (ty_var "a" loc))
         Pos (ty_var "a" loc)) :: sigM) in
  let envM, sigM = infer gamma0 modl in
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
       Format.fprintf ppf "val %s : %a\n%!" (Symbol.to_string v) (print_typeterm Pos) t
    | SDef (f, _) ->
       Format.fprintf ppf "def %s : %a\n%!" (Symbol.to_string f) (print_typeterm Pos) t in
  List.iter2 print sigm elems
