open Variance
open Typector
open Types
open Exp

module SMap = Symbol.Map

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

let constrain' loc err p n =
  let success = ref true in
  List.iter (fun e -> success := false; err e) (Types.constrain loc p n);
  !success

let dump_scheme ctx title {environment; expr} =
  Format.printf "%a\n%!" (print_automaton ctx title) (fun f ->
    f "out" expr;
    SMap.iter (fun n s -> f (Symbol.to_string n) s) environment)

let constrain loc ctx err name (inputs : (state * state) list) output =
  let dump title =
    let find_states f =
      let id = ref 0 in
      List.iter (fun (s, t) ->
                 f (Printf.sprintf "s-%d" !id) s;
                 f (Printf.sprintf "t-%d" !id) t;
                 incr id) inputs;
      f "out" output in
    Format.printf "%a\n%!" (print_automaton ctx title) find_states in
  let debug = false in
  if debug then dump (name ^ "_before");
  let errs = (List.fold_left (fun rs (p, n) -> rs @ constrain loc p n) [] inputs) in
  List.iter err errs;
  if debug then dump (name ^ "_after");
  match errs with
  | [] -> output
  | _ :: _ -> compile_type ctx Pos (TZero Pos)

let ty_join a b =
  let (jN, jP) = Types.flow_pair () in
  let errs =
    Types.constrain Location.internal a jN @
    Types.constrain Location.internal b jN in
  assert (errs = []);
  jP

let ty_join_neg a b =
  let (jN, jP) = Types.flow_pair () in
  let errs =
    Types.constrain Location.internal jP a @
    Types.constrain Location.internal jP b in
  assert (errs = []);
  jN

let join_scheme s s' =
  { expr = ty_join s.expr s'.expr;
    environment = SMap.merge (fun k t1 t2 ->
      match t1, t2 with
      | Some t1, Some t2 -> Some (ty_join_neg t1 t2)
      | x, None | None, x -> x) s.environment s'.environment }

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
     Some (ty_join_neg a b))
(* Some (Types.join a b)) *)






module IntMap = Map.Make (struct type t = int let compare = compare end)

type field_list = Symbol.t list (* sorted by hash order, no collisions *)


type case_code = { case_scheme : scheme ; mutable case_used : bool ; case_loc : Location.t }
type case_matrix = (Exp.pat list * Types.state SMap.t * case_code) list

type pat_split =
  | PSNone
  | PSAny of case_matrix
  | PSInt of case_matrix IntMap.t * case_matrix
  | PSObj of (case_matrix * field_list) SMap.t * (case_matrix * field_list) option (* nonempty *)

(* union of cases *)
let combine_splits (vp, (p : pat_split)) (vq, (q : pat_split)) : state * pat_split =
  let combine_ints (pis, pdef) (qis, qdef) =
    PSInt (IntMap.merge (fun i pi qi -> match pi, qi with
    | Some pi, Some qi -> Some (pi @ qi)
    | Some pi, None -> Some (pi @ qdef)
    | None, Some qi -> Some (pdef @ qi)
    | None, None -> None) pis qis, pdef @ qdef) in

  let rec union_fieldlists pfs qfs = match pfs, qfs with
    | [], r | r, [] -> r
    | (pf :: pfs'), (qf :: qfs') when Symbol.hash pf = Symbol.hash qf ->
       if pf = qf then
         pf :: union_fieldlists pfs' qfs'
       else
         failwith "field hash collision"
    | (pf :: pfs') , (qf :: qfs') ->
       if Symbol.hash pf < Symbol.hash qf then
         pf :: union_fieldlists pfs' qfs
       else
         qf :: union_fieldlists pfs qfs' in

  let dummy_pat : Exp.pat = (Location.internal, Some PWildcard) in

  let rec expand_fields_to wide curr pats =
    match wide, curr, pats with
    | [], [], pats -> pats
    | [], _ :: _, _ ->
       assert false (* wide must be a superset of curr *)
    | _, _ :: _, [] ->
       assert false (* pats should be at least as long as curr *)
    | wf :: wide', [], pats ->
       dummy_pat :: expand_fields_to wide' [] pats
    | wf :: wide', cf :: curr', p :: pats' when wf = cf ->
       p :: expand_fields_to wide' curr' pats'
    | wf :: wide', cf :: _, _ :: _ ->
       assert (Symbol.hash wf < Symbol.hash cf);
       dummy_pat :: expand_fields_to wide' curr pats in

  let combine_objcases ((pcases : case_matrix), pfields) ((qcases : case_matrix), qfields) =
    let fields = union_fieldlists pfields qfields in
    let expand_case fs (ps, vars, e) =
      (expand_fields_to fields fs ps, vars, e) in
    (List.map (expand_case pfields) pcases @
       List.map (expand_case qfields) qcases,
     fields) in

  let combine_objs (ptags, pdef) (qtags, qdef) =
    PSObj (SMap.merge (fun tag ptag qtag -> match ptag, pdef, qtag, qdef with
           | Some pt, _, Some qt, _ -> Some (combine_objcases pt qt)
           | Some pt, _, None, Some qdef -> Some (combine_objcases pt qdef)
           | Some pt, _, None, None -> Some pt
           | None, Some pdef, Some qt, _ -> Some (combine_objcases pdef qt)
           | None, None, Some qt, _ -> Some qt
           | None, _, None, _ -> None) ptags qtags,
           match pdef, qdef with
           | Some pdef, Some qdef -> Some (combine_objcases pdef qdef)
           | x, None | None, x -> x) in

  let split = match p, q with
  | PSNone, x | x, PSNone -> x

  | PSAny ps, PSAny qs -> PSAny (ps @ qs)

  | PSAny ps, PSInt (qis, qdef) ->
     combine_ints (IntMap.empty, ps) (qis, qdef)
  | PSInt (pis, pdef), PSAny qs ->
     combine_ints (pis, pdef) (IntMap.empty, qs)
  | PSInt (pis, pdef), PSInt (qis, qdef) ->
     combine_ints (pis, pdef) (qis, qdef)

  (* PSAny ps for objects is PSObj (SMap.empty, Some (ps, [])) *)
  | PSAny ps, PSObj (qtags, qdef) ->
     combine_objs (SMap.empty, Some (ps, [])) (qtags, qdef)
  | PSObj (ptags, pdef), PSAny qs ->
     combine_objs (ptags, pdef) (SMap.empty, Some (qs, []))

  | PSObj (ptags, pdef), PSObj (qtags, qdef) ->
     combine_objs (ptags, pdef) (qtags, qdef)

  | PSInt _, PSObj _
  | PSObj _, PSInt _ -> failwith "incompatible patterns" in
  (ty_join_neg vp vq, split)


let rec split_cases (cases : case_matrix) : state * pat_split =
  match cases with
  | [] -> (Types.zero Neg, PSNone)
  | ((loc, None) :: _, _, _) :: _ ->
     failwith "parse error?"
  | ([], _, _) :: _ ->
     failwith "internal error: split but no columns"
  | ((loc, Some p) :: ps, vars, e) :: cases ->
     match p with
     | PWildcard ->
        combine_splits (Types.zero Neg, PSAny [ps, vars, e]) (split_cases cases)
     | PVar x ->
        assert (SMap.mem x vars);
        let ty = SMap.find x vars in
        let (v, sp) = combine_splits
          (Types.zero Neg, PSAny [ps, SMap.remove x vars, e]) 
          (split_cases cases) in
        (ty_join_neg v ty, sp)
     | PObject (tag, unsorted_subpats) ->
        let sorted = List.sort (fun (t, p) (t', p') ->
          compare (Symbol.hash t) (Symbol.hash t')) unsorted_subpats in
        let rec check_dups = function
          | [] | [_] -> ()
          | t :: ((t' :: _) as ts) ->
             if Symbol.hash t = Symbol.hash t' then failwith "duplicate labels";
             check_dups ts in
        let fields = List.map fst sorted in
        check_dups fields;
        let subpats = List.map snd sorted in
        let case = [subpats @ ps, vars, e] in
        let split = match tag with
          | None -> PSObj (SMap.empty, Some (case, fields))
          | Some t -> PSObj (SMap.singleton t (case, fields), None) in
        combine_splits (Types.zero Neg, split) (split_cases cases)
     | PInt n ->
        combine_splits (Types.zero Neg, PSInt (IntMap.singleton n [ps, vars, e], [])) (split_cases cases)
     | PAlt (p1, p2) ->
        split_cases ((p1 :: ps, vars, e) :: (p2 :: ps, vars, e) :: cases)


let rec dump_decision_tree pfx cases =
  match cases with
  | [] -> Printf.printf "%s nonexhuastive!\n" pfx;
  | ([], vars, case) :: rest ->
     Printf.printf "%s done\n" pfx;
  | cases ->
     let (pvar, split) = split_cases cases in
     match split with
     | PSNone ->
        Printf.printf "%s nonexhaustive2\n" pfx;
     | PSAny cases ->
        Printf.printf "%s any\n" pfx;
        dump_decision_tree pfx cases
     | PSInt (ints, def) ->
        Printf.printf "%s ints:\n" pfx;
        ints |> IntMap.iter (fun i cases ->
          Printf.printf "%s %d:\n" pfx i;
          dump_decision_tree (pfx ^ "  ") cases);
        Printf.printf "%s _:\n" pfx;
        dump_decision_tree (pfx ^ "  ") def
     | PSObj (tags, def) ->
        Printf.printf "%s objs:\n" pfx;
        let p k fields =
          Printf.printf "%s %s [" pfx k;
          List.iter (Printf.printf "%s ") (List.map Symbol.to_string fields);
          Printf.printf "]\n" in
        tags |> SMap.iter (fun k (cases, fields) ->
          p (Symbol.to_string k) fields;
          dump_decision_tree (pfx ^ "  ") cases);
        match def with
        | Some (cases, fields) ->
           p "_" fields;
          dump_decision_tree (pfx ^ "  ") cases
        | None -> ()



type pat_desc =
 { pvar : state;
   pcases : pat_type }
and fields = pat_desc SMap.t
and pat_type =
  | PTAny
  | PTInt
  | PTObj of fields SMap.t * fields option Lazy.t

(* IDEA: separate PTObj into two cases:
     PTObj of fields
     PTVar of fields SMap.t * fields option Lazy.t
   PTVar's default case is never opened, but may be used in merge_desc.
   pat_desc_to_type always ignores it *)
   

(* take the meet of two pat_descs,
   but with extra error checking
   (e.g. complain about int ⊓ { foo : int } rather than producing a meet type) *)
let rec merge_desc s { pvar ; pcases } { pvar = pvar'; pcases = pcases' } =
  { pvar = ty_join_neg pvar pvar';
    pcases = merge_desctypes s pcases pcases' }
and merge_desctypes s pcases pcases' = match pcases, pcases' with
  | PTAny, PTAny -> PTAny
  | PTAny, t | t, PTAny -> t
  | PTInt, PTInt -> PTInt
  | PTInt, PTObj _ | PTObj _, PTInt -> failwith "obj/int mismatch"
  | PTObj (tags, def), PTObj (tags', def') ->
     let tags = SMap.merge (fun tag pat pat' -> match pat, def, pat', def' with
       | Some obj, _, Some obj', _ -> Some (merge_fields (s ^ ", tag: " ^ Symbol.to_string tag) obj obj')
       | None, def, Some obj, _
       | Some obj, _, None, def ->
          (match Lazy.force def with
          | Some def ->
             Some (merge_fields (s ^ ", dtag: " ^ Symbol.to_string tag) obj def)
          | None ->
             failwith ("nonexhaustive because tag " ^ Symbol.to_string tag ^ " unmatched in " ^ s))
       | None, _, None, _ -> None) tags tags' in
     let def = lazy (match Lazy.force def, Lazy.force def' with
       | d, None | None, d -> None
       | Some def, Some def' -> Some (merge_fields s def def')) in
     PTObj (tags, def)
and merge_fields s obj obj' =
  SMap.merge (fun field pat pat' -> match pat, pat' with
    | Some pat, Some pat' -> Some (merge_desc (s ^ ", field: " ^ Symbol.to_string field) pat pat')
    | p, None | None, p -> p) obj obj'



(* case matrices:
  [] = failure
  [([], e); ...] = success, handle e
  [(ps, e); ...] = more matching *)

type match_desc = pat_desc list * scheme
let rec merge_match_descs (desc : match_desc) (desc' : match_desc) : match_desc = match desc, desc' with
  | ([], e), ([], e') ->
     [], join_scheme e e'
  | ([], _), (_ :: _, _)
  | (_ :: _, _), ([], _) -> failwith "bad match length" (* FIXME impossible? checked where? *)
  | (p :: ps, e), (p' :: ps', e') ->
     let (rs, re) = merge_match_descs (ps, e) (ps', e') in
     (merge_desc "adsf" p p' :: rs), re

(* For what sort of values is this case matrix exhaustive, and what is the result type? *)
let rec describe_cases (cases : case_matrix) : match_desc =
  match cases with
  | [] -> failwith "nonexhaustive"
  | ([], vars, case) :: rest ->
     List.iter (fun (ps, vars, e) -> assert (ps = []); assert (SMap.is_empty vars)) cases; (* FIXME check+error *)
     case.case_used <- true;
     [], case.case_scheme
  | cases ->
     let (pvar, split) = split_cases cases in
     match split with
     | PSNone ->
        failwith "nonexhaustive2"
     | PSAny cases ->
        let (rest, result) = describe_cases cases in
        ({ pvar; pcases = PTAny} :: rest), result
     | PSInt (ints, def) ->
        let (rest, result) =
          IntMap.fold (fun i cases desc ->
            merge_match_descs (describe_cases cases) desc)
            ints (describe_cases def) in
        ({ pvar; pcases = PTInt} :: rest), result
     | PSObj (tags, def) ->
        (* FIXME: probably unsound *)

(*
        if SMap.is_empty tags then
          let def = match def with
            | None -> failwith "internal error: empty PSObj"
            | Some (cases, fields) ->
               let (def, _) = describe_fields SMap.empty fields (describe_cases cases) in
               def in
          let rest, result = def in
          ({ pvar; pcases = PTObj (SMap.empty, lazy (Some def))} :: rest), result
          
        else
          let tags = SMap.map (fun (cases, fields) ->
            describe_fields SMap.empty fields (describe_cases cases)) tags in
          let res = SMap.fold (fun tag (_, desc) acc ->
            match acc with
            | Some acc -> Some (merge_match_descs desc acc)
            | None -> Some desc) tags None in
          let (rest, result) = match res with Some r -> r 
            | None -> failwith "internal error: empty tagged PSObj" in
          let def = lazy (match def with
            | None -> None
            | Some (cases, fields) -> 
               let (def, _) = describe_fields SMap.empty fields (describe_cases cases) in
               Some def) in
          ({ pvar; pcases = PTObj (SMap.map fst tags, def)} :: rest), result
*)
          
          

        let tags = SMap.map (fun (cases, fields) ->
          describe_fields SMap.empty fields (describe_cases cases)) tags in
        let def = match def with
          | None -> None
          | Some (cases, fields) ->
             Some (describe_fields SMap.empty fields (describe_cases cases)) in
        let (rest, result) =
          let res = 
            (* FIXME: is this sound? *)
            if SMap.is_empty tags then
              (match def with
              | None -> None
              | Some (_, desc) -> Some desc)
            else
              SMap.fold (fun tag (_, desc) acc ->
                match acc with
                | Some acc -> Some (merge_match_descs desc acc)
                | None -> Some desc) tags None in
          match res with Some r -> r | None -> failwith "internal error: empty PSObj" in
        let def = match def with None -> None | Some (def, _) -> Some def in
        ({ pvar; pcases = PTObj (SMap.map fst tags, lazy def)} :: rest), result

and describe_fields (acc : fields) fields (desc : match_desc) : fields * match_desc = match fields, desc with
  | [], d -> acc, d
  | (f :: fs), ([], e) -> failwith "internal error: bad case length"
  | (f :: fs), (p :: ps, e) ->
     describe_fields (SMap.add f p acc) fs (ps, e)


let rec variables_bound_in_pat err : pat list -> Location.t SMap.t = function
  | [] -> SMap.empty
  | (l, None) :: ps -> variables_bound_in_pat err ps
  | (l, Some p) :: ps -> 
     match p with
     | PWildcard -> 
        variables_bound_in_pat err ps
     | PVar v ->
        let vs = variables_bound_in_pat err ps in
        (match SMap.find v vs with
        | l' -> err (Error.Rebound (`Value, l, v, l')); vs
        | exception Not_found -> SMap.add v l vs)
     | PObject (_, fs) ->
        variables_bound_in_pat err (List.map snd fs @ ps)
     | PInt n -> 
        variables_bound_in_pat err ps
     | PAlt (p1, p2) ->
        let v1 = variables_bound_in_pat err (p1 :: ps) in
        let v2 = variables_bound_in_pat err (p2 :: ps) in
        SMap.merge (fun k v1 v2 -> match v1, v2 with
        | Some l, Some l' -> 
           Some l
        | (Some l, None) | (None, Some l) ->
           err (Error.Partially_bound (`Value, l, k));
           Some l
        | None, None ->
           None) v1 v2



let add_singleton v gamma loc =
  let (n, p) = Types.flow_pair () in
  let singleton = {
    environment = SMap.singleton v n;
    expr = p} in
  SMap.add v (to_dscheme singleton) gamma


open Exp
let var env arg t = try [t, SMap.find arg env] with Not_found -> []

let failure () =
  { environment = SMap.empty; expr = compile_type Typector.empty_context Pos (TZero Pos) }



let ctx0 =
  empty_context
  |> add_opaque_type () (Symbol.intern "int") []
  |> add_opaque_type () (Symbol.intern "unit") []
  |> add_opaque_type () (Symbol.intern "bool") []
  |> add_opaque_type () (Symbol.intern "list") [TParam (Some VPos, Symbol.intern "A")]

let (ty_int, ty_unit, ty_bool) =
  let f s loc = Typector.ty_named' ctx0 (Symbol.intern s) [] loc in
  (f "int", f "unit", f "bool")

let ty_list t loc =
  Typector.ty_named' ctx0 (Symbol.intern "list") [APos (t loc)] loc


let rec pat_desc_to_type { pvar; pcases } = 
  ty_join_neg pvar (match pcases with
  | PTAny -> Types.zero Neg
  | PTInt -> Types.cons Neg (ty_int Location.internal) (* FIXME loc *)
  | PTObj (tags, def) -> 
     let obj fs = SMap.map (fun p -> fun loc -> pat_desc_to_type p) fs in
     let t = 
       (* FIXME: laziness about def tag case *)
       if SMap.is_empty tags then
         ty_obj_cases (SMap.map obj tags) (match Lazy.force def with Some o -> Some (obj o) | None -> None) Location.internal
       else
         ty_obj_cases (SMap.map obj tags) None Location.internal in
     Types.cons Neg t)


let rec typecheck ctx err gamma = function
| (loc, Some exp) -> typecheck' ctx err gamma loc exp
| (loc, None) ->
   (* syntax error already logged by parser *)
   failure ()
and typecheck' ctx err gamma loc exp = match exp with
  | Var v ->
     (try clone_scheme (Location.one loc) (SMap.find v gamma)
      with Not_found -> (err (Error.Unbound (`Value, loc, v)); failure ()))

  | Lambda (params, body) ->
     let rec check_params gamma = function
       (* FIXME check for duplicate arguments *)
       (* FIXME check type parameters and type annotations *)
       | [] -> typecheck ctx err gamma body
       | (loc, (((Ppositional arg | Preq_keyword arg | Popt_keyword(arg, _)) as param), asc)) :: params ->
          let gamma = match asc with
            | Some t ->
               let (n, p) = Types.compile_type_pair ctx t in
               SMap.add arg (to_dscheme {
                 environment = SMap.singleton arg n;
                 expr = p}) gamma
            | None -> add_singleton arg gamma loc in
          let body_ty = check_params gamma params in
          let env = match param with
            | Popt_keyword (arg, default) ->
               let {environment = envD; expr = exprD} = typecheck ctx err gamma default in
               let (defaultN, defaultP) = Types.flow_pair () in
               let _ = constrain' loc err exprD defaultN in
               (match SMap.find arg body_ty.environment with
                | t -> let _ = constrain' loc err defaultP t in ()
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
       expr = constrain loc ctx err "rec" ((exp_ty.expr, recN) :: var) recP }

  | App (fn, args) ->
     let { environment = envF; expr = exprF } = typecheck ctx err gamma fn in
     let rec check_args env pos kwargs constraints = function
       | [] ->
          let (resN, resP) = Types.flow_pair () in
          { environment = env;
            expr = constrain loc ctx err "app"
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
       expr = constrain loc ctx err "seq" [(expr1, Types.cons Neg (ty_unit loc)); (expr2, expN)] expP }

  | Typed (e, ty) ->
     let {environment; expr} = typecheck ctx err gamma e in
     let (n, p) = Types.compile_type_pair ctx ty in
     { environment; expr = constrain loc ctx err "typed" [expr, n] p }

  | Unit ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_unit loc) }

  | Int n ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_int loc) }

  | Bool b ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_bool loc) }

  | If (cond, tcase, fcase) ->
     let {environment = envC; expr = exprC} = typecheck ctx err gamma cond in
     let {environment = envT; expr = exprT} = typecheck ctx err gamma tcase in
     let {environment = envF; expr = exprF} = typecheck ctx err gamma fcase in
     { environment = env_join err loc envC (env_join err loc envT envF);
       expr = constrain loc ctx err "if" [exprC, Types.cons Neg (ty_bool loc)]
         (ty_join exprT exprF) }
  | Nil ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_list (fun _ -> Types.zero Pos) loc) }
  | Cons (x, xs) ->
     let x_ty = typecheck ctx err gamma x in
     let xs_ty = typecheck ctx err gamma xs in
     let (xN, xP) = Types.flow_pair () and (xsN, xsP) = Types.flow_pair () in
     { environment = env_join err loc x_ty.environment xs_ty.environment;
       expr = constrain loc ctx err "cons" [x_ty.expr, xN;
                                xs_ty.expr, Types.cons Neg (ty_list (fun _ -> xsN) loc)] (Types.cons Pos (ty_list (fun _ -> ty_join xP xsP) loc)) }

(*
  | Match (e, nil, x, xs, cons) ->
     let e_ty = typecheck ctx err gamma e in
     let nil_ty = typecheck ctx err gamma nil in
     let cons_ty = typecheck ctx err (add_singleton x (add_singleton xs gamma loc) loc) cons in
     let (xN, xP) = Types.flow_pair () in
     let vars =
       (try [xP, SMap.find x cons_ty.environment] with Not_found -> []) @
       (try [Types.cons Pos (ty_list (fun _ -> xP) loc), SMap.find xs cons_ty.environment] with Not_found -> []) in
     { environment = env_join err loc e_ty.environment (env_join err loc nil_ty.environment (SMap.remove x (SMap.remove xs cons_ty.environment)));
       expr = constrain loc ctx err "match" ([e_ty.expr, Types.cons Neg (ty_list (fun _ -> xN) loc)] @ vars)
         (ty_join ctx err nil_ty.expr cons_ty.expr) }
*)
  | Match (scr, cases) ->
     let scr_schemes = List.map (typecheck ctx err gamma) scr in
     let scr_env = List.fold_left (fun e s -> env_join err loc e s.environment) SMap.empty scr_schemes in
     let cases : case_matrix = cases |> List.map (fun ((loc, pats), e) ->
       let bound = variables_bound_in_pat err pats in
       let gamma = 
         bound |> SMap.bindings |> List.map fst |>
             List.fold_left (fun gamma var -> add_singleton var gamma loc) gamma in
       let sch = typecheck ctx err gamma e in
       let vars = SMap.mapi (fun v loc -> 
         match SMap.find v sch.environment with
         | ty -> ty
         | exception Not_found -> Types.zero Neg) bound in
       let sch = {sch with environment = SMap.merge (fun v schenv bvar -> 
         match schenv, bvar with
         | Some _, Some _ -> assert (SMap.mem v vars); None
         | Some v, None -> schenv
         | None, _ -> None) sch.environment bound} in
       let case = { case_scheme = sch; case_loc = loc; case_used = false } in
       pats, vars, case) in
     dump_decision_tree "" cases;
     Printf.printf "%!";
     let (pats, result) = describe_cases cases in
     cases |> List.iter (fun (_, _, { case_loc; case_used }) ->
       if not case_used then err (Error.Unused_case case_loc));
     let rec bind_pats scrs pats = match scrs, pats with
       | [], [] -> ()
       | [], _ -> failwith "too many patterns"
       | _, [] -> failwith "not enough patterns"
       | scr :: scrs, pat :: pats ->
          Types.constrain loc scr.expr (pat_desc_to_type pat)
          |> List.iter err;
          bind_pats scrs pats in
     bind_pats scr_schemes pats;
     { expr = result.expr; environment = env_join err loc scr_env result.environment }

  | Object (tag, o) ->
     let (env, fields) = List.fold_right (fun (s, e) (env, fields) ->
        let {environment = env'; expr = expr'} = typecheck ctx err gamma e in
        if Typector.SMap.mem s fields then failwith "Duplicate field";
        (env_join err loc env env', Typector.SMap.add s (fun _ -> expr') fields)) o (SMap.empty, Typector.SMap.empty) in
     { environment = env; expr = Types.cons Pos (ty_obj_tag tag fields loc) }

  | GetField (e, field) ->
     let e_ty = typecheck ctx err gamma e in
     let (xN, xP) = Types.flow_pair () in
     { environment = e_ty.environment;
       expr = constrain loc ctx err "field" [e_ty.expr,
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
and signature = Typector.context * dstate sigitem list

let rec infer_module err modl : signature =
  let rec infer tyctx gamma = function
    | [] -> tyctx, SMap.empty, []
    | (loc, MType (t, p, body)) :: modl ->
       (* Type definition *)
       infer (add_type_alias err t p body tyctx) gamma modl
    | (loc, MOpaqueType (t, p)) :: modl ->
       infer (add_opaque_type err t p tyctx) gamma modl
    | (loc, MDef (f, p, body)) :: modl ->
       (* Possibly-recursive function *)
       let {environment = envF; expr = exprF} as tyF =
         typecheck' tyctx err gamma loc (Rec (f, (loc, Some (Lambda (p, body))))) in
       let ctxM, envM, sigM = infer tyctx (SMap.add f (to_dscheme tyF) gamma) modl in
       ctxM, env_join err loc envF envM, (SDef (f, exprF) :: sigM)
    | (loc, MLet (v, e)) :: modl ->
       let {environment = envE; expr = exprE} = typecheck tyctx err gamma e in
       let ctxM, envM, sigM = infer tyctx (add_singleton v gamma loc) modl in
       ctxM, env_join err loc envE (SMap.remove v envM),
       let (expN, expP) = Types.flow_pair () in
       (SLet (v, constrain loc tyctx err "let" ((exprE, expN) :: var envM v expP)
         expP) :: sigM) in
  let ctxM, envM, sigM = infer ctx0 gamma0 modl in
  assert (SMap.is_empty envM);
  let states = List.map (function SDef (f, t) -> t | SLet (v, t) -> t) sigM in
  let remap, dstates = Types.determinise states in
  Types.optimise_flow dstates;
  let minim = Types.minimise dstates in
  ctxM, List.map (function SDef (f, t) -> SDef (f, minim (remap t)) | SLet (v, t) -> SLet (v, minim (remap t))) sigM

let rec print_signature ppf ((ctx, sigm) : signature) =
  let elems = sigm
     |> Types.clone (fun f -> List.map (function SLet (_, t) | SDef (_, t) -> f (Location.one Location.internal) t))
     |> decompile_automaton in
  let print s t = match s with
    | SLet (v, _) ->
       Format.fprintf ppf "val %s : %a\n%!" (Symbol.to_string v) (print_typeterm ctx) t
    | SDef (f, _) ->
       Format.fprintf ppf "def %s : %a\n%!" (Symbol.to_string f) (print_typeterm ctx) t in
  List.iter2 print sigm elems
