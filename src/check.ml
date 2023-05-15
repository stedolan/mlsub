open Util
open Tuple_fields
open Exp
open Typedefs
open Types
open Error

let rec env_lookup_var env v =
  match env with
  | Env_nil -> Error (Bad_name (`Unknown, `Var, v.label))
  | Env_vals { vals = vs; rest; _ }
       when SymMap.mem v.label vs ->
     if v.shift = 0 then Ok (SymMap.find v.label vs) else
       env_lookup_var rest { v with shift = v.shift - 1 }
  | Env_types { rest; _ } | Env_vals {rest; _}->
     env_lookup_var rest v

let env_lookup_type_var env lvl loc name =
  match env_lookup_type_var env loc name with
  | Some v ->
     if not (Env_level.extends v.level lvl) then
       Error (Illformed_type (`Bound_crosses_levels name))
     else
       Ok v
  | None -> Error (Bad_name (`Unknown, `Type, name))

let syn_tjoin loc (a : (_, _) typ) (b : (_, _) typ) =
  let rec join conses keep = function
    | Ttop l :: _ -> Ttop l
    | Tjoin (a, b) :: rest -> join conses keep (a :: b :: rest)
    | (Tsimple _ | Tvar _) as k :: rest -> join conses (k :: keep) rest
    | Tcons c :: rest when Cons.is_bottom c -> join conses keep rest
    | Tcons c :: rest -> join (c :: conses) keep rest
    | Tpoly _ :: _ -> fail loc (Illformed_type `Join_poly)
    | [] ->
       let conses = List.rev conses in
       let keep = List.rev keep in
       let joinands =
         match conses with
         | [] -> keep
         | [c] -> Tcons c :: keep
         | c :: cs ->
            let c =
              List.fold_left (fun c1 c2 ->
                let c = Cons.join c1 c2 in
                let either = function
                  | [x],[] | [],[x] -> x
                  | _ ->
                     fail loc (Illformed_type `Join_multi_cons)
                in
                Cons.map ~pos:either ~neg:either c) c cs
            in
            Tcons c :: keep
       in
       List.fold_left tjoin (List.hd joinands) (List.tl joinands)
  in
  join [] [] [a;b]

let tcons loc cons = Tcons (Cons.make ~loc cons)

let rec typ_of_tyexp : 'a 'b . env -> Env_level.t -> tyexp -> ('a, 'b) typ =
  fun env lvl ty -> match ty with
  | None, loc -> fail loc Syntax
  | Some t, loc -> typ_of_tyexp' env lvl loc t
and typ_of_tyexp' : 'a 'b . env -> Env_level.t -> Location.t -> tyexp' -> ('a, 'b) typ =
  fun env lvl loc ty -> match ty with
  | Tnamed (name, _) ->
     (* FIXME shifting? *)
     let name = name.label in
     begin match lookup_named_type loc name with
     | Some t -> t
     | None ->
        match env_lookup_type_var env lvl (Some loc) name with
        | Ok v -> Tvar (Vrigid v)
        | Error e -> fail loc e
     end
  | Trecord (tag, fields) ->
     tcons loc (Record (Option.map fst tag, typs_of_tuple_tyexp env lvl fields))
  | Tfunc (args, res) ->
     tcons loc (Func (typs_of_tuple_tyexp env lvl args, typ_of_tyexp env lvl res))
  | Tparen t ->
     typ_of_tyexp env lvl t
  | Tjoin (a, b) ->
     syn_tjoin loc (typ_of_tyexp env lvl a) (typ_of_tyexp env lvl b)
  | Tforall (vars, body) ->
     let vars, name_ix = enter_polybounds env vars in
     let env, _rigvars = enter_rigid env vars name_ix in
     let body = close_typ_rigid ~ispos:true (env_level env) (typ_of_tyexp env (env_level env) body) in
     Tpoly { vars; body }

and typs_of_tuple_tyexp : 'a 'b . env -> Env_level.t -> tyexp tuple_fields -> ('a, 'b) typ tuple_fields =
  fun env lvl ts -> map_fields (fun _fn t -> typ_of_tyexp env lvl t) ts

and enter_polybounds : 'a 'b . env -> typolybounds -> (string Location.loc * ('a,'b) typ option) iarray * int SymMap.t =
  fun env vars ->
  let name_ix =
    vars
    |> List.mapi (fun i ((n, l), _bound) -> i, l, n)
    |> List.fold_left (fun smap ((i : int), loc, n) ->
      if SymMap.mem n smap then fail loc (Bad_name (`Duplicate, `Type, n));
      SymMap.add n i smap) SymMap.empty in
  let level = Env_level.extend (env_level env) in
  let stubs =
    vars
    |> List.map (fun (name,_) -> {name; upper=None})
    |> IArray.of_list in
  let mkbound rig_names _loc bound =
    match bound with
    | None -> None
    | Some b ->
       let temp_env = Env_types { level; rig_names; rig_defns = stubs; rest = env } in
       let bound = close_typ_rigid ~ispos:false level (typ_of_tyexp temp_env (env_level temp_env) b) in
       begin match bound with Tcons _ -> () | _ -> fail (snd b) (Illformed_type `Bound_not_cons) end;
       if not (check_simple bound) then fail (snd b) (Illformed_type `Bound_not_simple);
       Some bound
  in
  let name_ix, vars = IArray.map_fold_left (fun names ((name',loc) as name, bound) ->
    let names' = SymMap.add name' (SymMap.find name' name_ix) names in
    names', (name, mkbound names loc bound)) SymMap.empty (IArray.of_list vars) in
  vars, name_ix

let typ_of_tyexp env t = typ_of_tyexp env (env_level env) t

let unit loc = tcons loc (Record (None, Tuple_fields.collect_fields []))

module IR_Builder = struct

type syn_cont =
  | Named_cont of IR.cont IR.Binder.ref
  | Gen_cont of (IR.value -> IR.comp)

(* Can be used more than once *)
let name_cont cont f : IR.comp =
  match cont with
  | Named_cont k -> f k
  | Gen_cont g ->
     let x = IR.Binder.fresh ~name:"x" () in
     let k = IR.Binder.fresh ~name:"k" () in
     LetCont(k, [x], g (IR.var x),
             f (IR.Binder.ref k))

let maybe_dup_cont ~uses cont f =
  if uses <= 1 then f cont
  else name_cont cont (fun k -> f (Named_cont k))

let apply_cont cont v : IR.comp =
  match cont with
  | Named_cont k -> Jump(k, [v])
  | Gen_cont f -> f v

type exp = syn_cont -> IR.comp
type pat = IR.value -> IR.comp -> IR.comp

let eval_cont (e : exp) (cont : IR.value -> IR.comp) =
  e (Gen_cont cont)

let eval_cont_fields (fs : exp tuple_fields) (cont : IR.value tuple_fields -> IR.comp) =
  let final : IR.value FieldMap.t -> IR.comp =
    fun valmap ->
    cont (map_fields (fun fn _ -> FieldMap.find fn valmap) fs) in
  let add_field (acc : IR.value FieldMap.t -> IR.comp) fn e =
    fun valmap ->
    eval_cont e @@ fun v ->
    acc (FieldMap.add fn v valmap)
  in
  (Tuple_fields.fold_fields add_field final fs) FieldMap.empty

let eval_cont_list (es : exp list) (cont : IR.value list -> IR.comp) =
  let add_exp (acc : IR.value list -> IR.comp) exp =
    fun vals ->
    eval_cont exp @@ fun v ->
    acc (v :: vals)
  in
  List.fold_left add_exp cont es []

let apply_pat (p : pat) (v : IR.value) (body : IR.comp) =
  p v body


let literal lit : exp =
  fun k -> apply_cont k (Literal lit)

let var v =
  fun k -> apply_cont k (Var v)

let tuple tag fields =
  fun k ->
  eval_cont_fields fields @@ fun fs ->
  apply_cont k (Tuple (tag, fs))

(* FIXME lambda *)

let project e field =
  fun k ->
  eval_cont e @@ fun v ->
  let vfield = IR.Binder.fresh ~name:field () in  
  Project (v, ([Field_named field, vfield],
               apply_cont k (IR.var vfield)))

let apply fn args =
  fun k ->
  eval_cont fn @@ fun fn ->
  eval_cont_fields args @@ fun args ->
  let vret = IR.Binder.fresh ~name:"x" () in
  Apply (Func fn, args, [vret],
         apply_cont k (IR.var vret))

let trap s : exp =
  fun _k ->
  Trap s

end

module IRB = IR_Builder

open Elab

type 'e check_output =
  { elab: 'e elab;
    comp: IRB.exp }


type generalisation_mode = {
  mutable gen_level_acc: env_level option;
}

let fresh_gen_mode () : generalisation_mode =
  { gen_level_acc = None }

let mark_var_use_at_level ~(mode : generalisation_mode) lvl =
  mode.gen_level_acc <-
    match mode.gen_level_acc, lvl with
    | None, x | x, None -> x
    | Some l1, Some l2 ->
       Some (Env_level.min l1 l2)


let elab_gen (env:env) ~mode poly (fn : env -> ptyp * 'a elab * _ * 'rest) : ptyp * (typolybounds option * tyexp * 'a) elab * bool * 'rest =
  let rigvars', rig_names =
    match poly with
    | None -> IArray.empty, SymMap.empty
    | Some poly -> enter_polybounds env poly in

  let env', _rigvars = enter_rigid env rigvars' rig_names in
  let orig_ty, Elab (erq, ek), gen_level, rest = fn env' in
  wf_ptyp env' orig_ty;
  let can_generalise =
    match gen_level with
    | None -> true
    | Some lvl when Env_level.equal lvl (env_level env') -> true
    | lvl ->
       mark_var_use_at_level ~mode lvl;
       false
  in
  let map ~neg ~pos (ty, erq) =
    let ty = pos ~mode:`Poly ~index:0 ty in
    let erq = elabreq_map_typs erq ~index:0
                ~neg:(neg ~mode:`Elab)
                ~pos:(pos ~mode:`Elab)
    in
    (ty, erq)
  in
  let policy = if can_generalise then `Generalise else `Hoist env in
  let bvars, (ty, erq) = promote ~policy ~rigvars:rigvars' ~env:env' ~map (orig_ty, erq) in
  if Vector.length bvars = 0 then
    ty, Elab (Pair(Ptyp ty, erq), fun (t,e) -> None, t, ek e), can_generalise, rest
  else
    let next_name = ref 0 in
    let rec mkname () =
      let n = !next_name in
      incr next_name;
      let name = match n with
        | n when n < 26 -> Printf.sprintf "%c" (Char.chr (Char.code 'A' + n))
        | n -> Printf.sprintf "T_%d" (n-26) in
      (* NB: look up env', to ensure no collisions with rigvars *)
      match env_lookup_type_var env' (env_level env') None name with
      | Error _ -> name, Location.noloc
      | Ok _ -> mkname () in
    let bounds = bvars |> Vector.to_array |> Array.map (function Gen_rigid rv -> IArray.get rigvars' rv.var | Gen_flex r -> mkname (), Some r) |> IArray.of_array in
    let tpoly = Tpoly { vars = bounds; body = ty } in
    wf_ptyp env tpoly;
    tpoly,
    Elab (Gen{bounds; body=Pair(Ptyp ty, erq)}, fun (poly, (t,e)) -> Some poly, t, ek e),
    can_generalise,
    rest

(* FIXME:
   Can't decide whether this makes types better or worse! *)
(*let elab_ptyp = function
  | Tsimple (Lower(fv, ctor)) as ty when is_bottom (Lower(Fvset.empty,ctor)) ->
     (match (fv :> flexvar list) with
      | [fv] -> Elab (Ntyp (Tsimple fv), fun x -> x)
      | _ -> Elab (Ptyp ty, fun x -> x))
  | ty ->
     Elab (Ptyp ty, fun x -> x)*)

let rec pat_name = function
  | Some (Pparens p), _ -> pat_name p
  | Some (Pbind (v,_)), _ -> Some (fst v : string)
  | _ -> None
  
let fresh_flow env =
  let fv = fresh_flexvar (env_level env) in
  Tsimple fv, Tsimple (of_flexvar fv)

type ty_mode =
  | Checking of ntyp
  | Inference of ptyp ref

let inspect_poly = function
  | Checking (Tpoly p) -> Some p
  | _ -> None

type inspect_result =
  | Imatches of (ptyp, ntyp) Cons.t
  (* FIXME: add Ifailed for when a Cons clearly does not match? *)
  | Iother

let inspect_cons cons = function
  | Checking (Tsimple _) ->
     (* bidirectional checking does not look inside Tsimple *)
     Iother
  | Checking (Tpoly _) ->
     (* FIXME: maybe make this impossible? *)
     Iother
  | Checking (Tcons c) ->
     (match Cons.get_single_sub cons c with Some c -> Imatches c | _ -> Iother)
  | Checking (Ttop _ | Tvar _ | Tjoin _) | Inference _ -> Iother

let rec check env ~(mode : generalisation_mode) e (ty : ty_mode) : exp check_output =
  (match ty with
   | Checking ty -> wf_ntyp env ty
   | Inference _ -> ());
  match e with
  | None, loc -> fail loc Syntax
  | Some e, loc ->
     let e = check' env ~mode loc e ty in
     { elab = (let* e = e.elab in Some e, loc);
       comp = e.comp }

(* FIXME: default is to infer & subtype, but we probably shouldn't
   even attempt this on intro forms at the wrong type. e.g. checking
   (1,2) against int *)
and check' env ~mode eloc e ty : exp' check_output =
  let inferred inf =
    match ty with
    | Checking ty ->
       subtype env inf ty |> or_raise `Expr eloc
    | Inference slot ->
       slot := join_ptyp env !slot inf
  in
  match e with
  | Lit l ->
     let lty, e = infer_lit l in
     inferred lty;
     e

  | Var (id, loc) ->
     begin match env_lookup_var env id with
     | Ok v ->
        mark_var_use_at_level ~mode v.gen_level;
        inferred v.typ;
        { elab = elab_pure e;
          comp = IRB.var v.comp_var }
     | Error e -> fail loc e
     end

  | Typed (e, ty) ->
     let t = typ_of_tyexp env ty in
     inferred t;
     let e = check env ~mode e (Checking t) in
     { elab = (let* e = e.elab in Typed (e, ty));
       comp = e.comp }

  | Parens e ->
     let e = check env ~mode e ty in
     { elab = (let* e = e.elab in Parens e);
       comp = e.comp }

  | If (e, ifso, ifnot) ->
     let e = check env ~mode e (Checking (tcons (snd e) Bool)) in
     let ifso = check env ~mode ifso ty in
     let ifnot = check env ~mode ifnot ty in
     { elab = (let* e = e.elab and* ifso = ifso.elab and* ifnot = ifnot.elab in
               If (e, ifso, ifnot));
       comp = fun k ->
         IRB.name_cont k @@ fun k ->
         IRB.eval_cont e.comp @@ fun cond ->
         Match(cond, [
           (IR.Symbol.of_string "true", ([], ifso.comp (Named_cont k)));
           (IR.Symbol.of_string "false", ([], ifnot.comp (Named_cont k)))], None) }

  | Tuple (tag, fields) ->
     if fields.fopen = `Open then failwith "invalid open tuple ctor";
     let target_ty = Cons.Record(Option.map fst tag,
                            map_fields (fun _ _ -> ()) fields) in
     let fields =
       (* FIXME: simplify here? *)
       match inspect_cons target_ty ty with
       | Imatches (Record (_, tf)) ->
          let infer_typed env ((_,loc) as e) =
            let ty, e = infer env ~mode e in
            { elab =
                (let* e = e.elab and* ty = elab_ptyp ty in
                 Some (Typed (e, ty)), loc);
              comp = e.comp }
          in
          merge_fields fields tf
            ~both:(fun _fn e ty -> Some (check env ~mode e (Checking ty)))
            ~left:(fun _fn e -> Some (infer_typed env e))
            ~right:(fun fn _ty -> failwith ("missing " ^ string_of_field_name fn) )
            ~extra:(function
              | _, (`Closed, `Extra) -> failwith "extra"
              | (`Open, _), _ -> failwith "invalid open tuple ctor" (* no open tuples *)
              | (`Closed, `Extra), _ -> failwith "missing"
              | _ -> `Closed)
       | _ ->
          let fields = map_fields (fun _fn e -> infer env ~mode e) fields in
          inferred (tcons eloc (Record (Option.map fst tag,
                                        map_fields (fun _ (ty, _e) -> ty) fields)));
          map_fields (fun _fn (_ty, e) -> e) fields
     in
     { elab =
         (let* ef = elab_fields (map_fields (fun _fn e -> e.elab) fields) in
          Tuple (tag, ef));
       comp =
         (let tag = Option.map (fun (t,_) -> IR.Symbol.of_string t) tag in
          IRB.tuple tag (map_fields (fun _fn e -> e.comp) fields)) }

  | Proj (e, (field, loc)) ->
     let ty, e = infer env ~mode e in
     let f = Field_named field in
     let (), tyf =
       match
        match_typ env ty eloc
         (Record (None,
                  { fields = FieldMap.singleton f ();
                   fnames = [Field_named field]; fopen = `Open }))
       with
       | Ok (Record (_, r)) -> FieldMap.find f r.fields
       | Ok _ -> assert false
       | Error c -> fail eloc (Conflict (`Expr, c)) in
     inferred tyf;
     { elab =
         (let* e = e.elab in Proj (e, (field, loc)));
       comp = IRB.project e.comp field }

  | Let (p, pty, rhs, body) ->
     let pty, e, gen_level = check_rhs env ~mode pty rhs in

     let case : case = ([[p]], snd p), body in
     let act, split = Check_pat.split_cases ~matchloc:(snd p) env [pty, gen_level] [case] in
     let act = Util.as_singleton act in
     let env = extend_env env act in
     let body = check env ~mode body ty in
     { elab =
         (let* e = e.elab and* pty = elab_ptyp pty and* body = body.elab in
          Let(p, Some pty, e, body));
       comp = fun k ->
         let actions = [| { act with Check_pat.rhs = body.comp } |] in
         IRB.eval_cont e.comp @@ fun e ->
         Check_pat.compile ~cont:k ~actions [e] split
     }

  | Seq (e1, e2) ->
     let e1 = check env ~mode e1 (Checking (unit eloc)) in
     let e2 = check env ~mode e2 ty in
     { elab = (let* e1 = e1.elab and* e2 = e2.elab in Seq (e1, e2));
       comp = fun k ->
         IRB.eval_cont e1.comp @@ fun _v ->
         e2.comp k }

  (* FIXME should I combine Tpoly and Func? *)
  | Fn ((poly, params, ret, body) as fndef) ->
     begin match inspect_poly ty with
     | Some {vars; body} ->
        (* rigvars not in scope in body, so no rig_names *)
        let env', open_rigvars = enter_rigid env vars SymMap.empty in
        let body = open_rigvars body in
        check' env' ~mode eloc e (Checking body)
        (* FIXME: Can there be flexvars used somewhere? Do they get bound/hoisted properly? *)
     | None ->
        let target_ty = Cons.Func (map_fields (fun _ _ -> ()) params, ()) in
        match poly, inspect_cons target_ty ty with
       | None, Imatches (Func (ptypes, rtype)) ->
          (* If poly <> None, then we should infer & subtype *)
          (* FIXME: do we need another level here? Does hoisting break things? *)
          let param_list = Tuple_fields.list_fields params in
          let param_list =
            param_list |> List.map (fun (fn, (pat, pty)) ->
              let ty = Tuple_fields.get_field ptypes fn in
              let ty_level =
                match pty with
                | None -> ty, Some (env_level env)
                | Some pty ->
                   let t = typ_of_tyexp env pty in
                   subtype env ty t |> or_raise `Pat (snd pty);
                   t, None
              in
              fn, pat, ty_level
            )
          in
          let param_ptyps = List.map (fun (_fn, _p, tl) -> tl) param_list in
          let case : case =
            ([List.map (fun (_fn, p, _tl) -> p) param_list], eloc), body
          in
          let act, split =
            Check_pat.split_cases ~matchloc:eloc env param_ptyps [case] in
          let act = Util.as_singleton act in

          let env' = extend_env env act in
          let body = check env' ~mode body (check_annot env' ret rtype) in
          { elab =
              (let* body = body.elab in
               (* No elaboration. Arguably we could *delete* annotations here! *)
               Fn (None, params, ret, body));
            comp = fun k ->
              let params = map_fields (fun _fn (p,_ty) -> IR.Binder.fresh ?name:(pat_name p) ()) params in
              let return = IR.Binder.fresh () in
              let cps: IR.value =
                let actions = [| { act with rhs = body.comp } |] in

                let body =
                  Check_pat.compile
                    ~cont:(IRB.Named_cont (IR.Binder.ref return))
                    ~actions
                    (list_fields params |> List.map (fun (_fn, v) -> IR.var v))
                    split
                in
                (Lambda(map_fields (fun _ v -> v) params,
                                   return,
                                   body))
              in
              IRB.apply_cont k cps }
       | _ ->
          let ty, fndef, compfn = infer_func_def env ~mode eloc fndef in
          inferred ty;
          { elab = (let* fndef = fndef in Fn fndef);
            comp = fun k -> IRB.apply_cont k compfn }
     end

  | FnDef ((s, sloc), fndef, body) ->
     let fmode = fresh_gen_mode () in
     let fty, fndef, compfn = infer_func_def env ~mode:fmode eloc fndef in
     mark_var_use_at_level ~mode fmode.gen_level_acc;
     let cvar = IR.Binder.fresh ~name:s () in
     let binding = {typ = fty; gen_level = fmode.gen_level_acc; comp_var = IR.Binder.ref cvar} in
     let env = Env_vals { vals = SymMap.singleton s binding; rest = env } in
     let body = check env ~mode body ty in
     { elab =
         (let* fndef = fndef and* body = body.elab in
          FnDef((s,sloc), fndef, body));
       comp = fun k -> LetVal(cvar, compfn, body.comp k) }

  | App (f, args) ->
     let fty, f = infer env ~mode f in
     let tyargs, ((), tyret) =
       match
        match_typ env fty eloc (Func (args, ()))
       with
       | Ok (Func (a, r)) -> a, r
       | Ok _ -> assert false
       | Error e -> fail eloc (Conflict (`Expr, e)) in
     let args = map_fields (fun _fn (e, t) -> check env ~mode e (Checking t)) tyargs in
     inferred tyret;
     { elab =
         (let* f = f.elab and* args = elab_fields (map_fields (fun _fn f -> f.elab) args) in
          App(f, args));
       comp = IRB.apply f.comp (map_fields (fun _fn a -> a.comp) args)}

  | Match ((es, matchloc), cases) ->
     let es = List.map (infer env ~mode) es in
     (* FIXME is this the right gen_level? How does this work again? *)
     let gen_level = mode.gen_level_acc in
     let etyps, es = List.map (fun (t, _) -> t, gen_level) es, List.map snd es in
     let orig_actions, split = Check_pat.split_cases ~matchloc env etyps cases in
     let actions =
       List.map2 (fun act (_, exp) ->
         let env = extend_env env  act in
         check env ~mode exp ty)
         orig_actions cases
     in
     { elab =
         (let* es = elab_list (List.map (fun e -> e.elab) es)
          and* actions = elab_list (List.map (fun e -> e.elab) actions) in
          Match((es, matchloc), List.map2 (fun (ps,_) e -> ps, e) cases actions));
       comp = fun k ->
         let actions = List.map2 (fun act act' -> {act with Check_pat.rhs = act'.comp}) orig_actions actions in
         let actions = Array.of_list actions in
         IRB.maybe_dup_cont ~uses:(Array.length actions) k @@ fun k ->
         IRB.eval_cont_list (List.map (fun e -> e.comp) es) @@ fun vals ->
         Check_pat.compile ~cont:k ~actions vals split
     }

  | Pragma ("true"|"false" as b) when match inspect_cons Bool ty with Imatches Bool -> true | _ -> false ->
     { elab = elab_pure e;
       comp = IRB.literal (Bool (String.equal b "true")) }
  | Pragma "bot" ->
     inferred (Tcons (Cons.bottom_loc eloc));
     { elab = elab_pure e;
       comp = IRB.trap "@bot" }
  | Pragma s -> failwith ("pragma: " ^ s)


and infer env ~(mode : generalisation_mode) (e : exp) : ptyp * exp check_output =
  let ty = ref (Tcons Cons.bottom) in
  let e = check env ~mode e (Inference ty) in
  wf_ptyp env !ty;
  !ty, e

and infer_func_def env ~mode eloc (poly, params, ret, body) : ptyp * func_def elab * IR.value =
   if params.fopen = `Open then failwith "invalid ... in params";
   let ty, elab, _generalised, (ecomp, (act, split)) =
     elab_gen env ~mode poly (fun env ->
       let params = map_fields (fun _fn (p, ty) ->
         match ty with
         | Some ty ->
            let ty = typ_of_tyexp env ty in
            (* check for contravariant joins *)
            ignore (close_typ_rigid ~ispos:false (env_level env) ty);
            (ty,ty), p, None
         | None ->
            fresh_flow env, p, Some (env_level env)) params in
       let param_list = Tuple_fields.list_fields params in
       let param_ptyps = List.map (fun (_fn, ((_tn, tp), _p, gen_level)) -> tp, gen_level) param_list in
       let case : case =
         ([List.map (fun (_fn, (_ty, p, _lvl)) -> p) param_list], eloc), body in
       let act, split = Check_pat.split_cases ~matchloc:eloc env param_ptyps [case] in
       let act = Util.as_singleton act in
       let env' = extend_env env act in

       let bmode = fresh_gen_mode () in
       let res, body =
         match ret with
         | Some ty ->
            let ty = typ_of_tyexp env ty in
            ignore (close_typ_rigid ~ispos:true (env_level env) ty);
            ty, check env' ~mode:bmode body (Checking ty)
         | None ->
            infer env' ~mode:bmode body in
       let _ = map_fields (fun _fn ((tn,tp),_,_) -> wf_ntyp env tn; wf_ptyp env tp) params in
       (* FIXME params or ptys? What happens if they disagree? *)
       tcons eloc (Func (map_fields (fun _fn ((tn,_tp),_,_) -> tn) params, res)),
       body.elab, bmode.gen_level_acc,
       (body.comp, (act, split))) in
   let fndef =
     let* poly, ty, body = elab in
     let tparams, tret =
       match ty with
       | Some (Tfunc (p,r)), _ -> p, r
       | ty -> intfail "what? %a" pp_tyexp ty in
     let params =
       merge_fields params tparams
         ~left:(fun _ _ -> assert false)
         ~right:(fun _ _-> assert false)
         ~both:(fun _fn (p, _) t -> Some (p, Some t))
         ~extra:(fun ((c, _),_) -> c) in
  (*     let poly =
       let mark = if generalised then [] else [("NOPOLY", Location.mark), None] in
       match poly with
       | None -> if mark = [] then None else Some mark
       | Some p -> Some (mark @ p)
     in*)
     (poly, params, Some tret, body) in
   let cps : IR.value =
     let actions = [| { act with rhs = ecomp } |] in
     let params = map_fields (fun fn _ -> IR.Binder.fresh ?name:(pat_name (fst (get_field params fn))) ()) params in
     let ret = IR.Binder.fresh() in
     Lambda(map_fields (fun _fn v -> v) params,
            ret,
            Check_pat.compile ~cont:(IRB.Named_cont (IR.Binder.ref ret)) ~actions (list_fields params |> List.map (fun (_,v) -> IR.var v)) split)
   in
   ty, fndef, cps

 
and extend_env env act =
  let vals = act.Check_pat.bindings |> SymMap.map (fun (typ, gen_level, var) ->
     { typ; comp_var = IR.Binder.ref var; gen_level }) in
  Env_vals { vals; rest = env }

and infer_lit = function
  | l, loc ->
     infer_lit' loc l,
     { elab = elab_pure (Lit (l, loc));
       comp = IRB.literal l }
and infer_lit' loc = function
  | Bool _ -> tcons loc Bool
  | Int _ -> tcons loc Int
  | String _ -> tcons loc String

and check_rhs env ~mode pty e =
  match pty with
  | None ->
     let bmode = fresh_gen_mode () in
     let pty, e = infer env ~mode:bmode e in
     mark_var_use_at_level ~mode bmode.gen_level_acc;
     pty, e, bmode.gen_level_acc
  | Some ty ->
     let t = typ_of_tyexp env ty in
     t, check env ~mode e (Checking t), None

and check_annot env annot ty =
  wf_ntyp env ty;
  match annot with
  | None -> Checking ty
  | Some ty' ->
     let t = typ_of_tyexp env ty' in
     subtype env t ty |> or_raise `Subtype (snd ty');
     Checking t
