open Util
open Error
open Exp
open Typedefs

module FieldMap = Tuple_fields.FieldMap

let syn_tjoin loc (a : (_, _) typ) (b : (_, _) typ) =
  match a, b with
  | Tsimple _, _ | _, Tsimple _ -> intfail "syn_tjoin: Tsimple"
  | Tpoly _, _ | _, Tpoly _ ->
     fail loc (Illformed_type `Join_poly)
  | Tcvj (cons_a, var_a, _loc_a),
    Tcvj (cons_b, var_b, _loc_b) ->
     if
       cons_a |> List.exists (fun (ca,_) ->
         cons_b |> List.exists (fun (cb,_) ->
           not (Cons1.incomparable_head ca cb)))
     then
       fail loc (Illformed_type `Join_multi_cons);
     let cons = cons_a @ cons_b in
     let vars = var_a @ List.filter (fun v -> not (List.exists (fun v' -> compare_typ_var v v' = 0) var_a)) var_b in
     Tcvj (cons, vars, Some loc)

type lookup_fn =
  env:env -> string loc -> tyarg list -> type_decl option

let default_lookup_fn ~env (name, _loc) _ = Env.lookup_decl env name

let rec typ_of_tyexp : 'a 'b . lookup:lookup_fn -> env:env -> tyexp -> ('a, 'b) typ =
  fun ~lookup ~env ty -> match ty with
  | None, loc -> fail loc Syntax
  | Some t, loc -> typ_of_tyexp' ~lookup ~env loc t
and typ_of_tyexp' : 'a 'b . lookup:lookup_fn -> env:env -> Location.t -> tyexp' -> ('a, 'b) typ =
  fun ~lookup ~env loc ty -> match ty with
  | Ttyvar (name, loc) ->
     begin match env_lookup_type_var env loc name with
     | Some v -> tvar (Vrigid v)
     | None -> fail loc (Bad_name (`Unknown, `Type, name))
     end
  | Trecord (Some (Named_tag ("Any", _)), [], _) ->
     tcons (Top, loc)
  | Trecord (Some (Named_tag ("Nothing", _)), [], _) ->
     tbot (Some loc)
  | Trecord (tag, args, fields) ->
     let check_arg name (v, (argname,_loc)) (i, arg) =
       let check p loc = function
         | `Strict | `Yes -> ()
         | `No -> fail loc (Illformed_type (`Wrong_args (name, `Variance (i, argname, p))))
       in
       let ok_pos loc t = check `Pos loc v.occurs_pos; typ_of_tyexp ~lookup ~env t in
       let ok_neg loc t = check `Neg loc v.occurs_neg; typ_of_tyexp ~lookup ~env t in
       match arg with
       | None, loc -> fail loc Syntax
       | Some arg, loc ->
          match arg with
          | Arg_pos t ->
             None, Some (ok_pos loc t)
          | Arg_neg t ->
             Some (ok_neg loc t), None
          | Arg_both {neg;pos} ->
             Some (ok_neg loc neg), Some (ok_pos loc pos)
          | Arg_gen t ->
             let ty = typ_of_tyexp ~lookup ~env t in
             (match v.occurs_neg with
              | `No -> None
              | `Yes -> Some ty),
             (match v.occurs_pos with
              | `No -> None
              | `Yes | `Strict -> Some ty)
     in
     let tag, args =
       match tag with
       | None | Some (Anon_tag | Struct_tag _) -> tag, []
       | Some (Named_tag (name,nameloc)) ->
          match lookup ~env (name,nameloc) args with
          | None -> fail nameloc (Bad_name (`Unknown, `Type, name))
          | Some decl ->
             let nparams = List.length decl.params in
             let nargs = List.length args in
             if nparams <> nargs then
               fail loc (Illformed_type (`Wrong_args (name, `Arity (nparams, nargs))));
             Some (Named_tag decl.name),
             List.map2 (check_arg name) decl.params (List.mapi (fun i x -> i,x) args)
     in
     let body, fopen = typs_of_fields ~lookup ~env (fields,loc) in
     tcons (Record {tag; args; body; fopen}, loc)
  | Tfunc (args, res) ->
     tcons (Func (List.map (typ_of_tyexp ~lookup ~env) args, typ_of_tyexp ~lookup ~env res), loc)
  | Tjoin (a, b) ->
     syn_tjoin loc (typ_of_tyexp ~lookup ~env a) (typ_of_tyexp ~lookup ~env b)
  | Tforall (vars, body) ->
     let vars, name_ix = enter_polybounds ~lookup ~env vars in
     let env, _rigvars = Types.enter_rigid env vars name_ix in
     let body =
       try Types.close_typ_poly_exn ~ispos:true (Env.level env) (typ_of_tyexp ~lookup ~env body)
       with Types.CloseError (err, errloc) ->
         let loc = Option.value errloc ~default:loc in
         fail loc (Illformed_type (`Close_error err))
     in
     Tpoly { vars; body }

and typs_of_fields : 'a 'b . lookup:lookup_fn -> env:env -> tyexp fields loc -> ('a,'b) typ Fields.t * Exp.extensible_flag =
  fun ~lookup ~env (fields,loc) ->
  let fields, fopen = Exp.record_fields ~loc fields in
  let fnames = List.map (fun ((f,_), _, _) -> f) fields in
  let fields = List.fold_left (fun acc ((f,floc), m, ty) ->
    let ty : _ Fields.field_desc =
      match m, ty with
      | Optional, Some (Some (Ttyvar ("absent", _)), _) ->
         Fabsent floc
      | Mandatory, Some (Some (Ttyvar ("absent", _)), _) ->
         Fbroken {abs_loc=floc; pres_loc=floc}
      | Optional, None ->
         Funknown floc
      | Optional, Some ty ->
         Foptional (typ_of_tyexp ~lookup ~env ty, {abs_loc=floc; pres_loc=floc})
      | Mandatory, Some ty ->
         Fpresent (typ_of_tyexp ~lookup ~env ty, floc)
      | Mandatory, None ->
         fail loc Syntax
    in FieldMap.add f ty acc)
    FieldMap.empty
    fields
  in
  {fields; fnames}, fopen

and enter_polybounds : 'a 'b . lookup:lookup_fn -> env:env -> typolybounds -> (string Location.loc * ('a,'b) typ option) iarray * int SymMap.t =
  fun ~lookup ~env vars ->
  let name_ix =
    vars
    |> List.mapi (fun i ((n, l), _bound) -> i, l, n)
    |> List.fold_left (fun smap ((i : int), loc, n) ->
      match SymMap.find n smap with
      | _, loc' -> fail loc (Bad_name (`Duplicate loc', `Type, n));
      | exception Not_found -> SymMap.add n (i,loc) smap)
      SymMap.empty
    |> SymMap.map fst in
  let level = Env_level.extend (Env.level env) in
  let stubs =
    vars
    |> List.map (fun (name,_) -> {name; upper=[Top,Location.noloc]})
    |> IArray.of_list in
  let mkbound rig_names loc bound =
    match bound with
    | None -> None
    | Some b ->
       let temp_env = Env.extend_types env ~level ~rig_names ~rig_defns:stubs in
       let bound =
         try Types.close_typ_poly_exn ~ispos:false level (typ_of_tyexp ~lookup ~env:temp_env b)
         with Types.CloseError (err,errloc) ->
           let loc = Option.value errloc ~default:loc in
           fail loc (Illformed_type (`Close_error err))
       in
       begin match bound with Tcvj (_,[],_) -> () | _ -> fail (snd b) (Illformed_type `Bound_not_cons) end;
       if not (Types.check_simple bound) then fail (snd b) (Illformed_type `Bound_not_simple);
       Some bound
  in
  let name_ix, vars = IArray.map_fold_left (fun names ((name',loc) as name, bound) ->
    let names' = SymMap.add name' (SymMap.find name' name_ix) names in
    names', (name, mkbound names loc bound)) SymMap.empty (IArray.of_list vars) in
  vars, name_ix
