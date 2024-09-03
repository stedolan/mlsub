open Error
open Util

module SymSet = Set.Make (struct
  type t = Exp.symbol
  let compare (s,_) (t,_) = String.compare s t
end)

module SymTbl = Hashtbl.Make (struct
  type t = Exp.symbol
  let equal (s,_) (t,_) = String.equal s t
  let hash (s,_) = Hashtbl.hash (s : string)
end)

let rec free_type_names = function
  | None, _ -> SymSet.empty
  | Some t, _ -> free_type_names' t
and free_type_names' =
  let open Exp in function
  | Tforall (vars, body) ->
     (* No possibility of capture: we're not binding named types, just Ttyvars *)
     List.fold_left SymSet.union (free_type_names body)
       (List.concat_map (fun (_, b) -> Option.to_list (Option.map free_type_names b)) vars)
  | Ttyvar _ ->
     SymSet.empty (* free *named type* names, not vars *)
  | Trecord (tag, args, fs) ->
     let free_arg = function
       | None, _ -> SymSet.empty
       | Some (Arg_pos t | Arg_neg t | Arg_gen t), _ -> free_type_names t
       | Some (Arg_both {neg;pos}), _ -> SymSet.union (free_type_names neg) (free_type_names pos)
     in
     let names =
       match tag with
       | Some (Named_tag id) -> SymSet.singleton id
       | Some (Struct_tag _ | Anon_tag) | None -> SymSet.empty
     in
     let names = List.fold_left (fun acc arg -> SymSet.union acc (free_arg arg)) names args in
     SymSet.union names (free_type_names_fields fs)
  | Tfunc (args, ret) ->
     List.fold_left SymSet.union (free_type_names ret) (List.map free_type_names args)
  | Tjoin (a, b) ->
     SymSet.union (free_type_names a) (free_type_names b)
and free_type_names_fields fs =
  fs
  |> Exp.record_fields ~loc:Location.noloc |> fst
  |> List.concat_map (fun (_,_,t) -> Option.to_list (Option.map free_type_names t))
  |> List.fold_left SymSet.union SymSet.empty

type scc_state =
  { index: int;
    mutable lowlink: int;
    mutable on_stack: bool }

type param_state =
  { name: Exp.symbol;
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
     |> List.fold_left SymSet.union SymSet.empty


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

let env_with_params ~env (params : Exp.symbol list) : Typedefs.env =
  let open Typedefs in
  let level = Env_level.extend (Env.level env) in
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

let check_prog (program : Exp.decl list) =
  let program_parts =
    program
    |> List.map (function
      | None, loc -> fail loc Syntax
      | Some (Exp.Dfn (s, fndef)), _loc -> Either.Right (s, fndef)
      | Some (Exp.Dtype (s, ps, body)), _loc -> Either.Left (s, ps, body))
  in
  let types, fns = List.partition_map Fun.id program_parts in
  ignore fns;
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
    |> SymSet.elements
    |> List.filter_map (fun s -> SymTbl.find_opt table s)
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
      SymTbl.add temp_decls d.name Typedefs.{name=d.name; params=vs; body=Decl_primitive});
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
      let open Typedefs in
      let env = env_with_params ~env (d.params |> List.map (fun (x:param_state) -> x.name)) in
      let ck_fields = Check_type.typs_of_fields ~lookup ~env in
      let body =
        match d.body with
        | Dty_record fs -> Decl_record (ck_fields fs)
        | Dty_variant vs -> Decl_variant (List.map (fun (s, fs) -> s, ck_fields fs) vs)
      in
      let body =
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
            fail loc (Illformed_type (`Misused_param (spec, fst p.name, vtype)));
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
           let walk_cons = function
             | Typedefs.Cons1.Record {tag=Some (Named_tag t); args; body}, loc ->
                assert (Typedefs.Fields.is_empty body);
                let params =
                  match SymTbl.find tbl t with
                  | decl' ->
                     found_recursion ~loc var decl';
                     List.map (fun (p : param_state) -> p.var_found) decl'.params
                  | exception Not_found ->
                     let decl' = Option.get (Typedefs.Env.lookup_decl env (fst t)) in
                     List.map fst decl'.params
                in
                List.iter2
                  (fun (param : Exp.variance_spec) ((neg, pos) : _ Typedefs.Cons1.tyarg) ->
                    begin match param.occurs_neg with
                    | `No -> ()
                    | `Yes -> Option.iter (walk ~decl (vneg var) ~index) neg
                    end;
                    begin match param.occurs_pos with
                    | `No -> ()
                    | `Strict -> Option.iter (walk ~decl var ~index) pos
                    | `Yes -> Option.iter (walk ~decl (vpos var) ~index) pos
                    end)
                  params args
             | cons, _loc ->
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
         let trim_cons = function
           | (Typedefs.Cons1.Record {tag=Some (Named_tag t); args; body}, loc) when SymTbl.mem tbl t ->
              let decl = SymTbl.find tbl t in
              let trim_arg (param : param_state) (n,p) =
                (if param.var_found.occurs_neg = `No then None else Option.map trim_args n),
                (if param.var_found.occurs_pos = `No then None else Option.map trim_args p)
              in
              let args = List.map2 trim_arg decl.params args in
              let body = Typedefs.Fields.map ~pos:trim_args body in
              (Typedefs.Cons1.Record {tag=Some (Named_tag t); args; body}, loc)
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
        (* FIXME: these two checks can safely be nonfatal warnings *)
        begin match variance.occurs_neg, ps.var_supplied_neg with
        | `No, Some loc ->
           fail loc (Illformed_type (`Wrong_args (fst decl.name, `Variance (ps.index, fst ps.name, `Neg))))
        | _ -> ()
        end;
        begin match variance.occurs_pos, ps.var_supplied_pos with
        | `No, Some loc ->
           fail loc (Illformed_type (`Wrong_args (fst decl.name, `Variance (ps.index, fst ps.name, `Pos))))
        | _ -> ()
        end;
        variance, ps.name)
      in
      {name = decl.name; params; body})
    |> Typedefs.Env.extend_decls env) Typedefs.Env.empty
  in
  Typedefs.wf_env env;
  env,
  program_parts |> List.filter_map (function
    | Either.Left ((s,_loc), _, _) -> Some (Option.get (Typedefs.Env.lookup_decl env s))
    | Either.Right _ -> None)

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
       Dty_variant (vs |> List.map (fun (s,fs) -> s, (unparse_fields fs, Location.noloc)))
  in
  Some (Dtype (name, params, body)), Location.noloc
