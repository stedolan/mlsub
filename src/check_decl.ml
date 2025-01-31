open Error
open Util


module SymMap = Typedefs.SymLocMap
module Nom_tag = Typedefs.Nom_tag
module TagSet = Set.Make (Nom_tag)

module SymTbl = Hashtbl.Make (struct
  type t = Exp.symbol
  let equal (s,_) (t,_) = String.equal s t
  let hash (s,_) = Hashtbl.hash (s : string)
end)

let rec free_type_names = function
  | None, _ -> TagSet.empty
  | Some t, _ -> free_type_names' t
and free_type_names' =
  let open Exp in function
  | Tforall (vars, body) ->
     (* No possibility of capture: we're not binding named types, just Ttyvars *)
     List.fold_left TagSet.union (free_type_names body)
       (List.concat_map (fun (_, b) -> Option.to_list (Option.map free_type_names b)) vars)
  | Ttyvar _ ->
     TagSet.empty (* free *named type* names, not vars *)
  | Trecord (tag, args, fs) ->
     let free_arg = function
       | None, _ | Some Arg_none, _ -> TagSet.empty
       | Some (Arg_pos t | Arg_neg t | Arg_gen t), _ -> free_type_names t
       | Some (Arg_both {neg;pos}), _ -> TagSet.union (free_type_names neg) (free_type_names pos)
     in
     let names =
       match tag with
       | Some (Named_tag id) -> TagSet.singleton (Record_tag id)
       | Some (Qualified_tag (s, t)) -> TagSet.singleton (Variant_tag (Vtag s,t))
       | Some (Struct_tag _ | Anon_tag) | None -> TagSet.empty
     in
     let names = List.fold_left (fun acc arg -> TagSet.union acc (free_arg arg)) names args in
     TagSet.union names (free_type_names_fields fs)
  | Tfunc (args, ret) ->
     List.fold_left TagSet.union (free_type_names ret) (List.map free_type_names args)
  | Tjoin (a, b) ->
     TagSet.union (free_type_names a) (free_type_names b)
  | Ttop | Tbot -> TagSet.empty
and free_type_names_fields fs =
  let fs, _ = Exp.record_fields ~loc:Location.noloc fs in
  fs
  |> List.map (fun (_,t) -> free_type_names_field t)
  |> List.fold_left TagSet.union TagSet.empty
and free_type_names_field (t : _ Exp.exp_field) =
  match t with
  | Mandatory (Some t) | Optional (Some t) -> free_type_names t
  | _ -> TagSet.empty

type scc_state =
  { index: int;
    mutable lowlink: int;
    mutable on_stack: bool }

type param_state =
  { name: Exp.symbol option;
    index: int;
    var_spec: Exp.variance_spec option;
    (* Variance as used in definition. Always <= var_spec (if present) *)
    mutable var_found: Exp.variance_spec;
    (* Variance as used in recursive applications *)
    mutable var_supplied_neg: Location.t option;
    mutable var_supplied_pos: Location.t option;
  }


type type_decl_state =
  { name: Exp.symbol;
    decl_index: int;
    params: param_state list;
    body: Exp.type_decl_body;
    mutable scc_state: scc_state option }

let decl_names (d : type_decl_state) =
  match d.body with
  | Dty_record (fs,_) -> free_type_names_fields fs
  | Dty_variant vs ->
     vs
     |> List.map (fun (_,(fs,_)) -> free_type_names_fields fs)
     |> List.fold_left TagSet.union TagSet.empty


module Variance_spec = struct
  type t = Exp.variance_spec
  let top : t = {occurs_pos = `Yes; occurs_neg=`Yes}
  let bot : t = {occurs_pos = `No; occurs_neg=`No}

  let le (a : t) (b : t) =
    (match a.occurs_neg, b.occurs_neg with
     | `No, _ -> true
     | _, `Yes -> true
     | `Yes, `No -> false)
    &&
    (match a.occurs_pos, b.occurs_pos with
     | `No, _ -> true
     | _, `Yes -> true
     | `Strict, `Strict -> true
     | (`Yes|`Strict), `No -> false
     | `Yes, `Strict -> false)
end

type variance =
  | Vpos_strict
  | Vpos
  | Vneg

let env_with_params ~env (params : Exp.symbol option list) : Typedefs.env =
  let open Typedefs in
  let level = Env_level.extend (Env.level env) in
  let params =
    params
    |> List.mapi (fun i -> function
       | Some s -> s
       | None -> Printf.sprintf "$unused_param%d" i, Location.noloc)
  in
  let rig_defns =
    params
    |> List.map (fun name : rigvar_defn ->
      { name; upper = [Top,Location.noloc]} )
    |> IArray.of_list
  in
  let rig_names =
    params
    |> List.mapi (fun i x -> i, x)
    |> List.fold_left (fun acc (index,(s,loc)) ->
       match SymMap.find s acc with
       | exception Not_found -> SymMap.add s (index,loc) acc
       | (_,loc') -> fail loc (Bad_name (`Duplicate loc', `Type, s))) SymMap.empty
    |> SymMap.map fst
  in
  Env.extend_types env ~level ~rig_names ~rig_defns

let check_type_decls types =
  let table = SymTbl.create 10 in
  types |> List.iteri (fun decl_index ((name,loc) as s, params, body) ->
    match SymTbl.find table s with
    | {name=(_,loc'); _} ->
       fail loc (Bad_name (`Duplicate loc', `Type, name))
    | exception Not_found ->
       let params = params |> List.mapi (fun index (var_spec, name) : param_state ->
         { name; index; var_spec; var_found = Option.value var_spec ~default:Variance_spec.bot; var_supplied_neg = None; var_supplied_pos = None }) in
       SymTbl.add table s {name = s; decl_index; params; body; scc_state=None});
  (* Tarjan's SCC algorithm *)
  let components = ref [] in
  let stack = ref [] in
  let next_index = ref 0 in
  let rec strongconnect decl =
    assert (Option.is_none decl.scc_state);
    let index = !next_index in
    incr next_index;
    let state = { index; lowlink = index; on_stack = true } in
    decl.scc_state <- Some state;
    stack := decl :: !stack;
    decl_names decl
    |> TagSet.elements
    |> List.filter_map (fun s -> SymTbl.find_opt table (Nom_tag.type_name s))
    |> List.sort (fun d1 d2 -> compare d1.decl_index d2.decl_index)
    |> List.iter (fun decl' ->
      match decl'.scc_state with
      | None ->
         let state' = strongconnect decl' in
         state.lowlink <- min state.lowlink state'.lowlink
      | Some ({ on_stack = true; _ } as state') ->
         state.lowlink <- min state.lowlink state'.index
      | Some { on_stack = false; _ } ->
         ());
    if state.lowlink = state.index then begin
      let rec collect acc =
        match !stack with
        | { scc_state = Some ({ on_stack = true; _ } as state'); _ } as decl' :: rest ->
           state'.on_stack <- false;
           stack := rest;
           let acc = decl' :: acc in
           if decl' == decl then acc else collect acc
        | _ -> assert false
      in
      let scc = collect [] in
      components := scc :: !components
    end;
    state
  in
  types |> List.iter (fun (s, _, _) ->
    let decl = SymTbl.find table s in
    if Option.is_none decl.scc_state then ignore (strongconnect decl));
  let components = List.rev !components in

  (* Typecheck a whole strongly connected component simultaneously *)
  let env = components |> List.fold_left (fun env cs ->
    let tbl = SymTbl.create 10 in
    let temp_decls = SymTbl.create 10 in
    cs |> List.iter (fun d ->
      SymTbl.add tbl d.name d;
      let vs = d.params |> List.map (fun p -> Option.value p.var_spec ~default:Variance_spec.top, p.name) in
      let body : Typedefs.decl_body =
        match d.body with
        | Dty_record _ -> Decl_record Typedefs.Fields.empty
        | Dty_variant cases -> Decl_variant (SymMap.of_list (cases |> List.map (fun (s,_) -> s,Typedefs.Fields.empty)))
      in
      SymTbl.add temp_decls d.name Typedefs.{name=d.name; params=vs; body});
    let lookup ~env name args =
      match SymTbl.find tbl name with
      | exception Not_found -> Typedefs.Env.lookup_decl env (fst name)
      | decl ->
         if List.length args = List.length decl.params then begin
           List.iter2
             (fun param arg ->
               begin match param.var_supplied_neg, arg with
               | None, (Some (Exp.Arg_neg _ | Exp.Arg_both _), loc) ->
                  param.var_supplied_neg <- Some loc
               | _ -> ()
               end;
               begin match param.var_supplied_pos, arg with
               | None, (Some (Exp.Arg_pos _ | Exp.Arg_both _), loc) ->
                  param.var_supplied_pos <- Some loc
               | _ -> ()
               end)
             decl.params
             args
         end;
         Some (SymTbl.find temp_decls name)
    in
    let decl_types =
      cs |> List.map (fun (d : type_decl_state) ->
      let env = env_with_params ~env (d.params |> List.map (fun (x:param_state) -> x.name)) in
      let ck_fields fs = Check_type.typs_of_fields ~lookup ~env fs in
      let body : Typedefs.decl_body  =
        match d.body with
        | Dty_record fs -> Decl_record (ck_fields fs)
        | Dty_variant vs -> Decl_variant (List.map (fun (s, fs) -> s, ck_fields fs) vs |> SymMap.of_list)
      in
      let body =
        let open Typedefs in
        let nojoin ((_,_,tyloc) as ty) =
          if is_varjoin ty then
            let loc = Option.value tyloc ~default:(snd d.name) in
            fail loc (Illformed_type `Join_of_ty_param)
        in
        Typedefs.map_decl_body ~pos:(close_typ ~neg:nojoin ~pos:nojoin (Env.level env) 0) body
      in
      d, body)
    in
    let rec compute_variance () =
      let changed = ref false in
      let vneg = function
        | Vpos_strict | Vpos -> Vneg
        | Vneg -> Vpos
      in
      let vpos = function
        | Vpos_strict | Vpos -> Vpos
        | Vneg -> Vneg
      in
      let found_parameter ~loc ~decl variance i =
        let p = List.nth decl.params i in
        let vtype, var_found =
          match variance with
          | Vpos_strict -> `Pos, { p.var_found with occurs_pos = `Strict }
          | Vpos -> `Pos, { p.var_found with occurs_pos = `Yes }
          | Vneg -> `Neg, { p.var_found with occurs_neg = `Yes }
        in
        if not (Variance_spec.le var_found p.var_found) then begin
          assert (Variance_spec.le p.var_found var_found);
          let spec = Option.value p.var_spec ~default:Variance_spec.top in
          if not (Variance_spec.le var_found spec) then
            fail loc (Illformed_type (`Misused_param (spec, Option.map fst p.name, vtype)));
          changed := true;
          p.var_found <- var_found
        end
      in
      let found_recursion ~loc variance decl =
        match variance with
        | Vpos_strict | Vneg -> ()
        | Vpos ->
           fail loc (Illformed_type (`Recursion (`Not_strictly_positive (fst decl.name))))
      in
      let rec walk ~decl var ~index (ty : (zero,zero) Typedefs.typ) =
        match ty with
        | Tpoly { vars; body } ->
           vars |> IArray.iter (fun (_, bound) -> Option.iter (walk ~decl (vneg var) ~index:(index + 1)) bound);
           walk ~decl var ~index:(index + 1) body
        | Tsimple _ -> .
        | Tcvj (conses, vars, _loc) ->
           let walk_args ~tag ~loc args =
             let params =
               match tag with
               | Either.Left (Some Typedefs.Cons1.(Anon_tag | Struct_tag _) | None) -> []
               | Either.Left (Some (Named_tag t)) ->
                  begin match SymTbl.find tbl (Nom_tag.type_name t) with
                  | decl' ->
                     found_recursion ~loc var decl';
                     List.map (fun (p : param_state) -> p.var_found) decl'.params
                  | exception Not_found ->
                     List.map fst (Typedefs.Env.get_decl_params env t)
                  end
               | Either.Right (Nom_tag.Vtag s) ->
                  (* FIXME messy, dedup? *)
                  begin match SymTbl.find tbl s with
                  | decl' ->
                     found_recursion ~loc var decl';
                     List.map (fun (p : param_state) -> p.var_found) decl'.params
                  | exception Not_found ->
                     List.map fst (Typedefs.Env.lookup_decl env (fst s) |> Option.get).params
                  end
             in
             List.iter2
               (fun (param : Exp.variance_spec) (arg : _ Typedefs.Cons1.tyarg) ->
                 Typedefs.Cons1.Tyarg.iter arg
                   ~neg:(fun neg ->
                     match param.occurs_neg with
                     | `No -> ()
                     | `Yes -> walk ~decl (vneg var) ~index neg)
                   ~pos:(fun pos ->
                     match param.occurs_pos with
                     | `No -> ()
                     | `Strict -> walk ~decl var ~index pos
                     | `Yes -> walk ~decl (vpos var) ~index pos))
               params args;

           in
           let walk_cons = function
             | Typedefs.Cons1.Record {tag; args; body}, loc ->
                walk_args ~tag:(Left tag) ~loc args;
                ignore (Typedefs.Fields.map ~pos:(walk ~decl var ~index) body);
                ()
             | Variant_whole (tag, args), loc ->
                walk_args ~tag:(Right tag) ~loc args
             | (Top | Func _) as cons, _loc ->
                ignore (Typedefs.Cons1.map ~neg:(walk ~decl (vneg var) ~index) ~pos:(walk ~decl var ~index) cons)
           in
           let walk_var : Typedefs.typ_var -> unit = function
             | Vrigid _ -> assert false
             | Vbound v when v.index <> index -> ()
             | Vbound v ->
                found_parameter ~loc:v.loc ~decl var v.var
           in
           List.iter walk_cons conses;
           List.iter walk_var vars
      in
      decl_types |> List.iter (fun (decl, body) ->
        ignore (Typedefs.map_decl_body ~pos:(fun x -> walk ~decl Vpos_strict ~index:0 x; Typedefs.tbot None) body));
      if !changed then compute_variance ()
    in
    compute_variance ();

    let rec trim_args : 'z. (zero,zero) Typedefs.typ -> ('z,'z) Typedefs.typ =
      function
      | Tsimple _ -> .
      | Tpoly {vars; body} ->
         let vars = IArray.map (fun (v,bound) -> v,Option.map trim_args bound) vars in
         let body = trim_args body in
         Tpoly {vars; body}
      | Tcvj (conses, vars, loc) ->
         let trim_arglist params args =
           let trim_arg (param : param_state) (arg : _ Typedefs.Cons1.tyarg) =
             match param.var_spec, arg with
             | Some _, arg ->
                (* specified variance, no trimming *)
                Typedefs.Cons1.Tyarg.map ~neg:trim_args ~pos:trim_args arg
             | None, (Arg_none | Arg_pos _ | Arg_neg _) -> assert false
             | None, Arg_both (n, p) ->
                match param.var_found.occurs_neg, param.var_found.occurs_pos with
                | `No, `No -> Arg_none
                | `Yes, `No -> Arg_neg (trim_args n)
                | `No, (`Yes|`Strict) -> Arg_pos (trim_args p)
                | `Yes, (`Yes|`Strict) -> Arg_both (trim_args n, trim_args p)
           in
           List.map2 trim_arg params args
         in
         let trim_cons = function
           | (Typedefs.Cons1.Record {tag=Some (Named_tag t); args; body}, loc) when SymTbl.mem tbl (Nom_tag.type_name t) ->
              let decl = SymTbl.find tbl (Nom_tag.type_name t) in
              let args = trim_arglist decl.params args in
              let body = Typedefs.Fields.map ~pos:trim_args body in
              (Typedefs.Cons1.Record {tag=Some (Named_tag t); args; body}, loc)
           | (Typedefs.Cons1.Variant_whole (Vtag tag, args), loc) when SymTbl.mem tbl tag ->
              let decl = SymTbl.find tbl tag in
              let args = trim_arglist decl.params args in
              (Typedefs.Cons1.Variant_whole (Vtag tag, args), loc)
           | (cons, loc) ->
              (Typedefs.Cons1.map ~neg:trim_args ~pos:trim_args cons, loc)
         in
         Tcvj (List.map trim_cons conses, vars, loc)
    in

    decl_types
    |> List.map (fun (decl, body) -> decl, Typedefs.map_decl_body ~pos:trim_args body)
    |> List.map (fun (decl, body) : Typedefs.type_decl ->
      let params = decl.params |> List.map (fun (ps : param_state) ->
        let variance = ps.var_found in
        begin match variance.occurs_neg, ps.var_supplied_neg with
        | `No, Some loc ->
           Error.log ~loc (Illformed_type (`Wrong_args (fst decl.name, `Variance (ps.index, Option.map fst ps.name, `Neg))))
        | _ -> ()
        end;
        begin match variance.occurs_pos, ps.var_supplied_pos with
        | `No, Some loc ->
           Error.log ~loc (Illformed_type (`Wrong_args (fst decl.name, `Variance (ps.index, Option.map fst ps.name, `Pos))))
        | _ -> ()
        end;
        variance, ps.name)
      in
      {name = decl.name; params; body})
    |> Typedefs.Env.extend_decls env) Typedefs.Env.empty
  in
  Typedefs.wf_env env;
  env

let check_prog (program : Exp.decl list) =
  let types =
    program
    |> List.filter_map (function
      | None, loc -> fail loc Syntax
      | Some (Exp.Dtype (s, ps, body)), _loc -> Some (s, ps, body)
      | Some (Exp.Dfn _), _ -> None)
  in
  let env = check_type_decls types in
  let env, prog_rev =
    List.fold_left
      (fun (env, acc) decl ->
        let env, (decl : Elab.typed_decl) =
          match decl with
          | None, loc -> fail loc Syntax
          | Some (Exp.Dtype ((s,_), _, _)), _ ->
             env, Dtype (Option.get (Typedefs.Env.lookup_decl env s))
          | Some (Exp.Dfn ((s,sloc), fndef)), loc ->
             let mode = Check.fresh_gen_mode () in
             let typ, tfndef = Check.infer_func_def env ~loc:sloc ~mode ~name:s loc fndef in
             let cvar = IR.Binder.fresh ~name:s () in
             let binding = Typedefs.{typ; gen_level = mode.gen_level_acc; comp_var = IR.Binder.ref cvar; used=false} in
             let env = Typedefs.Env.extend_vals env ~vals:(Typedefs.SymMap.singleton s binding) in
             env, Dfn ((s,sloc), tfndef)
        in
        env, decl :: acc)
      (env, [])
      program
  in
  env, List.rev prog_rev

let unparse_type_decl ~env (d : Typedefs.type_decl) : Exp.decl =
  let Typedefs.{name; params; body} = d in
  let params = List.map (fun (v,p) -> Some v, p) params in
  let env = env_with_params ~env (List.map snd params) in
  let body : Exp.type_decl_body =
    let unparse_fields =
      Typedefs.unparse_fields
        ~pos:(Typedefs.unparse_gen_typ
                ~env:(env,[])
                ~neg:(fun ~env:_ -> never)
                ~pos:(fun ~env:_ -> never))
        ~tag:(Some ())
    in
    let body =
      let getrv (conses, vars, loc) vars' =
        let open Typedefs in
        let vars = vars @ (List.map (fun (var,loc) -> Vrigid {level=Env.level env;loc;var}) vars') in
        Tcvj (conses, vars, loc)
      in
      let openrig t = Typedefs.open_typ ~neg:getrv ~pos:getrv 0 t in
      Typedefs.map_decl_body body ~pos:openrig in
    match body with
    | Decl_primitive ->
       unimp "Primitive syntax"
    | Decl_record fs ->
       Dty_record (unparse_fields fs, Location.noloc)
    | Decl_variant vs ->
       Dty_variant (vs |> SymMap.map (fun fs -> (unparse_fields fs, Location.noloc)) |> SymMap.bindings)
  in
  Some (Dtype (name, params, body)), Location.noloc

let unparse_decl ~env (d : Elab.typed_decl) : Exp.decl =
  match d with
  | Dtype d ->
     unparse_type_decl ~env d
  | Dfn (s, fndef) ->
     let fndef = Elab.Elaborate.fndef (env, []) fndef in
     Some (Dfn (s, fndef)), Location.noloc
