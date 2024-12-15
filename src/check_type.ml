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
  | Ttop ->
     tcons (Top, loc)
  | Tbot ->
     tbot (Some loc)
  | Trecord (tag, args, fields) ->
     let check_arg name (v, (argname,_loc)) (i, arg) : _ Cons1.tyarg =
       let bad_variance p loc =
         fail loc (Illformed_type (`Wrong_args (name, `Variance (i, argname, p))))
       in
       let has_pos = match v.occurs_pos with `Yes | `Strict -> true | `No -> false in
       let has_neg = match v.occurs_neg with `Yes -> true | `No -> false in
       let ok_pos loc t = if not has_pos then bad_variance `Pos loc; typ_of_tyexp ~lookup ~env t in
       let ok_neg loc t = if not has_neg then bad_variance `Neg loc; typ_of_tyexp ~lookup ~env t in
       match arg with
       | None, loc -> fail loc Syntax
       | Some arg, loc ->
          match arg with
          | Arg_pos t ->
             let t = ok_pos loc t in
             if has_neg
             then Arg_both (tbot (Some loc), t)
             else Arg_pos t
          | Arg_neg t ->
             let t = ok_neg loc t in
             if has_pos
             then Arg_both (t, ttop loc)
             else Arg_neg t
          | Arg_both {neg; pos} ->
             Arg_both (ok_neg loc neg, ok_pos loc pos)
          | Arg_gen t ->
             let t = typ_of_tyexp ~lookup ~env t in
             match has_neg, has_pos with
             | false, false -> Arg_none
             | true, false -> Arg_neg t
             | false, true -> Arg_pos t
             | true, true -> Arg_both (t,t)
     in
     let (tag : Typedefs.Cons1.Tag.t option), args, override_decl =
       let check_args ~name ~params =
         let nparams = List.length params in
         let nargs = List.length args in
         if nparams <> nargs then
           fail loc (Illformed_type (`Wrong_args (fst name, `Arity (nparams, nargs))));
         List.map2 (check_arg (fst name)) params (List.mapi (fun i x -> i,x) args)
       in
       match tag with
       | None -> None, [], None
       | Some Anon_tag -> Some Anon_tag, [], None
       | Some (Struct_tag s) -> Some (Struct_tag s), [], None
       | Some (Qualified_tag (name, case)) ->
          begin match lookup ~env name args with
          | None -> fail (snd name) (Bad_name (`Unknown, `Type, fst name))
          | Some { body = Decl_primitive | Decl_record _; _ } ->
             fail (snd case) (Bad_name (`Unknown, `Type, fst case))
          | Some { name; params; body = Decl_variant cases } ->
             match SymLocMap.find_opt case cases with
             | None -> fail (snd case) (Bad_name (`Unknown, `Type, fst case))
             | Some fs ->
                let tag = Typedefs.Nom_tag.Variant_tag (name, case) in
                Some (Named_tag tag),
                check_args ~name ~params,
                Some (tag, fs)
          end
       | Some (Named_tag (name,nameloc)) ->
          begin match lookup ~env (name,nameloc) args with
          | None -> fail nameloc (Bad_name (`Unknown, `Type, name))
          | Some { name; params; body = Decl_variant _ } ->
             fixme; (* bad tag here, should be alias *)
             let tag = Typedefs.Nom_tag.Record_tag name in
             Some (Named_tag tag),
             check_args ~name ~params,
             None
          | Some { name; params; body = Decl_primitive } ->
             let tag = Typedefs.Nom_tag.Record_tag name in
             Some (Named_tag tag),
             check_args ~name ~params,
             None
          | Some { name; params; body = Decl_record fs } ->
             let tag = Typedefs.Nom_tag.Record_tag name in
             Some (Named_tag tag),
             check_args ~name ~params,
             Some (tag, fs)
          end
     in
     let body = typs_of_fields ~lookup ~env (fields,loc) in
     begin match override_decl with
     | Some (ntag, fields) when not (Fields.is_empty body) ->
        begin match
          (* Check that the fields exist *)
          Types.Fields.sub ~f:(fun _fn _ty _exp -> ())
            (body, fun _ -> Fields.Fbroken {abs_loc=loc;pres_loc=loc} (*bottom*))
            (fields, fun _ -> Fabsent loc)
        with
        | Ok () -> ()
        | Error err ->
           let err, fn, cploc, cnloc =
             match err with
             | Field_missing (name, ploc, nloc) ->
                Types.Field_missing name, Some name, ploc, nloc
             | Field_extra (name, ploc, nloc) ->
                Types.Field_extra name, name, ploc, nloc
           in
           let err = Types.make_err env err
                       (Record {tag; args; body = body}, cploc)
                       (Record {tag; args; body = fields}, cnloc)
           in
           fail loc (Conflict (`Field_override (ntag, fn), err))
        end
     | _ -> ()
     end;
     tcons (Record {tag; args; body}, loc)
  | Tfunc (args, res) ->
     tcons (Func (List.map (typ_of_tyexp ~lookup ~env) args, typ_of_tyexp ~lookup ~env res), loc)
  | Tjoin (a, b) ->
     syn_tjoin loc (typ_of_tyexp ~lookup ~env a) (typ_of_tyexp ~lookup ~env b)
  | Tforall (vars, body) ->
     let vars, name_ix = enter_polybounds ~lookup ~env vars in
     let env, _rigvars, _rv2 = Types.enter_rigid env vars name_ix in
     let body =
       try Types.close_typ_poly_exn ~ispos:true (Env.level env) (typ_of_tyexp ~lookup ~env body)
       with Types.CloseError (err, errloc) ->
         let loc = Option.value errloc ~default:loc in
         fail loc (Illformed_type (`Close_error err))
     in
     Tpoly { vars; body }

and typs_of_fields : 'a 'b . lookup:lookup_fn -> env:env -> tyexp fields loc -> ('a,'b) typ Fields.t =
  fun ~lookup ~env (fields,loc) ->
  let fields, fields_ext = Exp.record_fields ~loc fields in
  if fields_ext <> Ext_closed then fail loc Syntax;
  let fnames = List.map (fun ((f,_), _) -> f) fields in
  let fields = List.fold_left (fun acc ((f,floc), ty) ->
    let ty : _ Fields.field_desc =
      match ty with
      | Absent ->
         Fabsent floc
      | Abs_broken ->
         Fbroken {abs_loc=floc; pres_loc=floc}
      | Optional None ->
         Funknown floc
      | Optional (Some ty) ->
         Foptional (typ_of_tyexp ~lookup ~env ty, {abs_loc=floc; pres_loc=floc})
      | Mandatory (Some ty) ->
         Fpresent (typ_of_tyexp ~lookup ~env ty, floc)
      | Mandatory None ->
         fail loc Syntax
    in FieldMap.add f ty acc)
    FieldMap.empty
    fields
  in
  {fields; fnames}

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
    |> List.map (fun (name,_) -> {name; upper=[Top,Location.noloc]; upper_promote_check=None})
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
