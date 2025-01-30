open Util
open Typedefs

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)


type close_typ_err =
  | Join_contravariant
  | Join_bad_scoping
exception CloseError of close_typ_err * Location.t option

let close_poly_neg ((_,_,loc) as ty) =
  if is_varjoin ty then
    raise (CloseError (Join_contravariant, loc))

let close_poly_pos ty =
  match is_locally_closed 0 (Tcvj ty) with
  | Ok () -> ()
  | Error loc -> raise (CloseError (Join_bad_scoping, Some loc))

let close_typ_poly_exn ~ispos lvl ty =
  if ispos
  then close_typ ~neg:close_poly_neg ~pos:close_poly_pos lvl 0 ty
  else close_typ ~neg:close_poly_pos ~pos:close_poly_neg lvl 0 ty

let tcons_head (c, loc) =
  let tunit _ = Tsimple () in
  tcons (Cons1.map ~neg:tunit ~pos:tunit c, loc)


type head_conflict =
  | Incompatible
  | Args of [`Too_few | `Too_many | `Wrong_number]
  | Expected_tag of (Exp.tuple_tag option * Cons1.tuple_tag list)

type conflict =
  | Head of head_conflict
  | Field_missing of Tuple_fields.field_name
  | Field_extra of Tuple_fields.field_name option

type err_typ = (unit, unit) typ

type subtyping_error = {
  lhs : err_typ;
  rhs : err_typ;
  err : conflict;
  located : (err_typ Location.loc * err_typ Location.loc);
  (* lhs, rhs use fst env alone,
     located uses (env,ext) *)
  env : env * string iarray list;
}

exception SubtypeError of subtyping_error

let close_err_rigid ~orig_env ~env vars {lhs; rhs; err; located; env = (_env', ext)} =
  (* Type errors should never involve flexible variables *)
  let close ix t = close_typ ~neg:ignore ~pos:ignore (Env.level env) ix t in
  let lhs =
    let tunit _ _ = Tsimple () in
    open_typ ~neg:tunit ~pos:tunit 0 (close 0 lhs)
  in
  let vars = vars |> IArray.map (fun ((s,l), bound) ->
    (freshen_name (env,ext) s, l),
    (Option.map (fun _ -> Tsimple ()) bound))
  in
  let rhs = Tpoly {vars; body=close 0 rhs} in
  let located =
    let (a,al), (b,bl) = located in
    (close (List.length ext) a,al), (close (List.length ext) b, bl)
  in
  let ext = ext @ [IArray.map (fun ((s,_),_) -> s) vars] in
  { lhs; rhs; err; located; env = (orig_env, ext) }

(* FIXME most uses are making fresh vars above/below something. Refactor? *)
let[@inline] noerror f = try f () with SubtypeError _ -> intfail "subtyping error should not be possible here!"


(*
 * Core subtyping functions
 *)

(* There are two ways to represent a constraint α ≤ β between two flexible variables.
   (I). Make the upper bound of α be UBvar β. (Ensure also that LB(β) contains LB(α))
   (II). Make the lower bound of β contain α. (Ensure also that UB(α) contains UB(β)) *)

let make_err' env err (lhs,lloc) (rhs,rloc) =
  { lhs; rhs; err;
    located = ((lhs,lloc), (rhs,rloc));
    env = (env, []) }

let make_err env err (cp,cploc) (cn,cnloc) =
  let lhs = tcons_head (cp, cploc) and rhs = tcons_head (cn, cnloc) in
  make_err' env err (lhs,cploc) (rhs,cnloc)

let wrap_cons_err (cp, cploc) (cn, cnloc) k err =
  let wrap_cons c inner =
    let f k' _ = if Cons1.equal_field k k' then inner else Tsimple () in
    Cons1.mapi c ~neg:f ~pos:f
  in
  let tl, tr =
    if Cons1.field_is_positive k
    then err.lhs, err.rhs
    else err.rhs, err.lhs
  in
  { err with
    lhs = tcons (wrap_cons cp tl, cploc);
    rhs = tcons (wrap_cons cn tr, cnloc) }


let rec map_typ_0 : 'neg1 'pos1 'neg2 'pos2 .
  neg:(index:int -> 'neg1 -> ('pos2, 'neg2) typ) ->
  pos:(index:int -> 'pos1 -> ('neg2, 'pos2) typ) ->
  ?neg_cons:(index:int -> ('pos2,'neg2) conses_typ -> ('pos2,'neg2) conses_typ) ->
  ?pos_cons:(index:int -> ('neg2,'pos2) conses_typ -> ('neg2,'pos2) conses_typ) ->
  index:int -> ('neg1, 'pos1) typ -> ('neg2, 'pos2) typ =
  fun ~neg ~pos ?neg_cons ?pos_cons ~index -> function
  | Tcvj (conses, vars, loc) ->
     let conses =
       Conses.map conses
         ~neg:(map_typ_0 ~pos:neg ~neg:pos ?neg_cons:pos_cons ?pos_cons:neg_cons ~index)
         ~pos:(map_typ_0 ~neg ~pos ?neg_cons ?pos_cons ~index)
     in
     let conses =
       match pos_cons with
       | None -> conses
       | Some f -> f ~index conses
     in
     Tcvj (conses, vars, loc)
  | Tsimple t -> pos ~index t
  | Tpoly {vars; body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (n, t) -> n, Option.map (map_typ_0 ~neg:pos ~pos:neg ?neg_cons:pos_cons ?pos_cons:neg_cons ~index) t) vars in
     let body = map_typ_0 ~neg ~pos ?neg_cons ?pos_cons ~index body in
     Tpoly {vars; body}

let map_typ_1 ~neg ~pos ~index t =
  let neg ~index:_ t = Tsimple (neg t) in
  let pos ~index:_ t = Tsimple (pos t) in
  map_typ_0 ~neg ~pos ~index t


let as_single_var ty vars =
  assert (is_tbot (Tcvj ty));
  match vars with
  | [i, _loc] -> i
  | _ -> assert false

let as_rigvar = function
  | Vbound _ -> intfail "Vbound"
  | Vrigid rv -> rv

let upper_rigvar rv =
  { urv_var = rv;
    urv_conses = ([Top,rv.loc],rv.loc) (*FIXME location?*);
    urv_ordered = ref (Some rv) }

let rec instantiate_flex env vars (body : ptyp) : ptyp =
  let fvars = IArray.map (fun _ -> fresh_flexvar (Env.level env)) vars in
  let fvneg ty vars =
    Tsimple (IArray.get fvars (as_single_var ty vars))
  in
  let fvpos ty vars =
    let t = ptyp_to_lower ~simple:true env (Tcvj ty) in
    Tsimple (t @ List.map (fun (v,_loc) -> Lflexvar (IArray.get fvars v)) vars)
  in
  IArray.iter2 (fun (fv : flexvar) (_,t) ->
    let b =
      match t with
      | None -> Utop
      | Some t -> ntyp_to_upper ~simple:true env (open_typ ~neg:fvpos ~pos:fvneg 0 t) in
    assert (fv.upper = Utop && fv.lower = []);
    fv_set_upper ~changes:(ref []) fv b)
    fvars vars;
  open_typ ~neg:fvneg ~pos:fvpos 0 body

and ptyp_to_lower ~simple env : ptyp -> lower = function
  | Tsimple l -> l
  | Tcvj (conses, vars, _loc) ->
     let conses =
       conses |> List.map (fun (cons, loc) ->
         Lcons (Cons1.map cons
                  ~neg:(ntyp_to_fresh_flexvar ~simple env)
                  ~pos:(ptyp_to_lower ~simple env),
                loc))
     in
     let vars = List.map (fun v -> Lrigvar (as_rigvar v)) vars in
     conses @ vars
  | Tpoly {vars; body} ->
     assert (not simple);
     let body = instantiate_flex env vars body in
     ptyp_to_lower ~simple env body

and ntyp_to_upper ~simple env : ntyp -> upper = function
  | Tsimple t -> Uflexvar t
  | t when is_ttop t -> Utop
  | Tcvj (conses, vars, loc) ->
     let conses =
       Conses.map conses
         ~neg:(ptyp_to_lower ~simple env)
         ~pos:(ntyp_to_fresh_flexvar ~simple env)
     in
     let rvs = List.map (fun v -> upper_rigvar (as_rigvar v)) vars in
     let loc = Option.value loc ~default:Location.(fixme "neg loc") in
     Ugen {conses = (conses, loc); rvs; higher_fvs = []}
  | Tpoly {vars; body} ->
     assert (not simple);
     (* Negative var occurrences should be replaced with their upper
        bounds, positive ones should be deleted. *)
     (* FIXME: assumes left-to-right scoping of bounds,
        which isn't enforced in user types *)
     let bounds = Array.init (IArray.length vars) (fun i ->
       let ((_,loc),_) = IArray.get vars i in ttop loc) in
     let neg ty vars = bounds.(as_single_var ty vars) in
     let pos ty _vars = Tcvj ty in
     vars |> IArray.iteri (fun i -> function
       | (_, None) -> ()
       | (_, Some b) -> bounds.(i) <- open_typ ~neg:pos ~pos:neg 0 b);
     let body = open_typ ~neg ~pos 0 body in
     ntyp_to_upper ~simple env body

and ntyp_to_fresh_flexvar ~simple env t =
  fresh_flexvar' (Env.level env) (ntyp_to_upper ~simple env t)

module Type_shape = struct

  type ('n1,'p1,'n2,'p2) t =
    { of_typ_pos : env:Env.t -> ('n2,'p2) typ -> 'p1;
      of_typ_neg : env:Env.t -> ('p2,'n2) typ -> 'n1;
      to_typ_pos : 'p1 -> ('n2,'p2) typ;
      to_typ_neg : 'n1 -> ('p2,'n2) typ }

  let negate t =
    { of_typ_pos = t.of_typ_neg;
      of_typ_neg = t.of_typ_pos;
      to_typ_pos = t.to_typ_neg;
      to_typ_neg = t.to_typ_pos }

  let of_typ ~env ~shape t = shape.of_typ_pos ~env t
  let to_typ ~shape t = shape.to_typ_pos t

  let simple_pos : (flexvar, lower, flexvar, lower) t =
    { of_typ_pos = (fun ~env t -> ptyp_to_lower ~simple:false env t);
      of_typ_neg = (fun ~env t -> ntyp_to_fresh_flexvar ~simple:false env t);
      to_typ_pos = (fun t -> Tsimple t);
      to_typ_neg = (fun t -> Tsimple t); }

  let simple_neg = negate simple_pos

  let gen : _ t =
    { of_typ_pos = (fun ~env:_ t -> t);
      of_typ_neg = (fun ~env:_ t -> t);
      to_typ_pos = Fun.id;
      to_typ_neg = Fun.id }

  let gen_pos = gen
  let gen_neg = gen
  let gen_unit = gen
end

module Fields = struct
  include Typedefs.Fields
  let merge ~f (a, a_def) (b, b_def) =
    let seen = Table.create 10 in
    let merge_field fn a b =
      let a =
        match a with
        | Some a -> a
        | None -> a_def fn
      in
      let b =
        match b with
        | Some b -> b
        | None -> b_def fn
      in
      let r = f a b in
      Table.add seen fn ();
      (* OPT: Consider dropping the field entirely if it's default with a_loc *)
      Some r
    in
    let fields = Map.merge merge_field a.fields b.fields in
    let check_name fn =
      if Table.mem seen fn
      then (Table.remove seen fn; true)
      else false
    in
    let fnames =
      let a_names = List.filter check_name a.fnames in
      let b_names = List.filter check_name b.fnames in
      a_names @ b_names
    in
    let r = { fields; fnames } in
    wf ~pos:ignore r; r

  let join ~pos a b =
    merge a b
      ~f:(fun a b -> match a, b with
         | (Funknown _ as x), _
         | _, (Funknown _ as x) -> x
         | x, Fbroken _
         | Fbroken _, x -> x
         | Foptional (a, l), (Foptional (b, _) | Fpresent (b, _)) -> Foptional (pos a b, l)
         | Foptional _ as a, (Fabsent _) -> a
         | Fpresent (a, l), Fpresent (b, _) -> Fpresent (pos a b, l)
         | Fpresent (a, pres_loc), Foptional (b, l) ->
            Foptional (pos a b, {l with pres_loc})
         | Fpresent (a, pres_loc), Fabsent abs_loc ->
            Foptional (a, {abs_loc; pres_loc})
         | Fabsent abs_loc, (Foptional (b, {pres_loc; _})) ->
            Foptional (b, {abs_loc; pres_loc})
         | Fabsent _ as a, (Fabsent _) -> a
         | Fabsent abs_loc, Fpresent (b, pres_loc) ->
            Foptional (b, {abs_loc; pres_loc}))

  (* Meet. Locations from lower side, from left if same *)
  let meet ~pos a b =
    let open One_or_two in
    merge a b
      ~f:(fun a b -> match a, b with
          | x, Funknown _ ->
             field_desc_map (fun x -> pos (L x)) x
          | Funknown _, x ->
             field_desc_map (fun x -> pos (R x)) x
          | (Fbroken _ as x), _
          | _, (Fbroken _ as x) -> x
          | Foptional (a, l), Foptional (b, _) ->
             Foptional (pos (LR (a, b)), l)
          | Foptional (a, _), Fpresent (b, l) ->
             Fpresent (pos (LR (a, b)), l)
          | Foptional _, (Fabsent _ as b) ->
             b
          | Fpresent (a, l), (Foptional (b, _) | Fpresent (b, _)) ->
             Fpresent (pos (LR (a, b)), l)
          | Fpresent (_, pres_loc), Fabsent abs_loc
          | Fabsent abs_loc, Fpresent (_, pres_loc) ->
             Fbroken {pres_loc; abs_loc}
          | (Fabsent _ as a), (Foptional _ | Fabsent _) ->
             a)

  type field_error =
    | Field_missing of Tuple_fields.field_name * Location.t * Location.t
    | Field_extra of Tuple_fields.field_name option * Location.t * Location.t

  exception FieldError of field_error
  let sub ?(extra=empty) ~f (a,a_def) (b,b_def) =
    let sub_field fn a b =
      let a =
        match a with
        | Some x -> x
        | None -> a_def fn
      in
      let b =
        match b with
        | Some x -> x
        | None -> b_def fn
      in
      begin match a, b with
      | _, Funknown _ -> ()
      | Fbroken _, _ -> ()
      | Fabsent _, (Fabsent _ | Foptional _) -> ()
      | (Foptional (a, _) | Fpresent (a, _)), Foptional (b, _)
      | Fpresent (a, _), Fpresent (b, _) ->
         f fn a b

      | (Funknown la | Fabsent la | Foptional (_, {abs_loc=la; _})),
        (Fpresent (_, lb) | Fbroken {pres_loc=lb; _})
      | (Funknown la, Foptional (_, {pres_loc=lb; _})) ->
         (* failed to be present *)
         raise (FieldError (Field_missing (fn, la, lb)))
      | (Funknown la | Foptional (_,{pres_loc=la;_}) | Fpresent (_, la)),
        (Fbroken {abs_loc=lb;_} | Fabsent lb) ->
         (* failed to be absent *)
         raise (FieldError (Field_extra (Some fn, la, lb)))
      end;
      None
    in
    match
      ignore (Map.merge sub_field a.fields b.fields);
      extra.fnames |> List.iter (fun k ->
        if not (Map.mem k a.fields || Map.mem k b.fields) then
          ignore (sub_field k None None));
    with
    | _ -> Ok ()
    | exception (FieldError e) -> Error e

end

module Cons1 = struct
  open Fields
  include Typedefs.Cons1

  let record_def ~env ~shape ~loc {tag; args; body=_} =
    match tag with
    | Some (Named_tag name) ->
       let decl_fields = Env.get_decl_fields env name in
       fun fn ->
       Fields.find fn (decl_fields, ())
       |> Option.value ~default:(Fields.Fabsent loc)
       |> Fields.field_desc_map (fun ty ->
         let neg ty vars =
           List.nth args (as_single_var ty vars)
           |> Tyarg.proj_neg
           |> Type_shape.to_typ ~shape:(Type_shape.negate shape)
         in
         let pos ty vars =
           List.nth args (as_single_var ty vars)
           |> Tyarg.proj_pos
           |> Type_shape.to_typ ~shape:shape
         in
         gen_zero ty
         |> open_typ ~neg ~pos 0
         |> Type_shape.of_typ ~env ~shape)
    | None -> fun _fn -> Funknown loc
    | Some (Anon_tag | Struct_tag _) -> fun _fn -> Fabsent loc

  let drop_record_tag ~shape env (r : _ Cons1.cons_record) =
    match r.tag with
    | None -> r
    | Some tag ->
       let body =
         match tag with
         | Anon_tag | Struct_tag _ -> r.body
         | Named_tag name ->
            let loc = Nom_tag.loc name in
            Fields.merge ~f:(fun ty _decl -> ty)
              (r.body, record_def ~env ~shape ~loc r)
              (Typedefs.Env.get_decl_fields env name, fun _ -> Fabsent loc)
       in
       {tag=None; args=[]; body}

  let expand_variant ~env tag args =
    Env.get_variant_subtags env tag
    |> List.map (fun tag -> Cons1.Record {tag=Some (Named_tag tag); args; body=Fields.empty})
end

let subtype_record_args ~neg ~pos a b =
  let sub_arg i (arg_a, arg_b) =
    ignore (Cons1.Tyarg.zip arg_a arg_b
              ~neg:(fun a b -> neg (Cons1.Named_arg (`Neg, i)) b a)
              ~pos:(fun a b -> pos (Cons1.Named_arg (`Pos, i)) a b))
  in List.iteri sub_arg (List.combine a b)

let subtype_record_body ~env ~shape_a ~shape_b ~neg ~pos ((a : _ Cons1.cons_record),a_loc) ((b : _ Cons1.cons_record),b_loc) =
  let open Cons1 in
  let a =
    match b.tag with
    | Some _ -> a
    | None -> Cons1.drop_record_tag ~shape:shape_a env a
  in
  (match a.tag with Some (Named_tag _) -> () | _ -> assert (a.args = []));
  (match b.tag with Some (Named_tag _) -> () | _ -> assert (b.args = []));
  subtype_record_args ~neg ~pos a.args b.args;
  let sub_field k a b = pos (Record_field k) a b in
  let a_def = record_def ~env ~shape:shape_a ~loc:a_loc a in
  let b_def = record_def ~env ~shape:shape_b ~loc:b_loc b in
  Fields.sub ~f:sub_field (a.body,a_def) (b.body,b_def)

let subtype_conses ~cnvars env ~shape_a ~shape_b ~neg ~pos (cp,cploc) (cns,cnloc) =
  let neg cp cn k a b =
    try neg a b
    with SubtypeError err -> raise (SubtypeError (wrap_cons_err cp cn k err))
  in
  let pos cp cn k a b =
    try pos a b
    with SubtypeError err -> raise (SubtypeError (wrap_cons_err cp cn k err))
  in
  let conflict () =
    let conflict : head_conflict =
      match cp with
      | Cons1.Func (pargs, _) ->
         begin match cns |> List.filter_map (function
           | Cons1.Func (args,_), _ -> Some (List.length args)
           | _ -> None)
         with
         | [n] when List.length pargs < n -> Args `Too_many
         | [n] when List.length pargs > n -> Args `Too_few
         | _::_ -> Args `Wrong_number
         | [] -> Incompatible
         end
      | Cons1.Record {tag=ptag; _} ->
         begin match cns |> List.filter_map (function
           | Cons1.Record {tag=Some t;_}, _ -> Some t
           | _ -> None) with
         | [] -> Incompatible
         | tags -> Expected_tag (Option.map Cons1.Tag.unparse ptag, tags)
         end
      | _ -> Incompatible
    in
    let err =
      let lhs = tcons_head (cp, cploc) in
      let err = Head conflict in
      let tunit _ = Tsimple () in
      let cns = Conses.map ~neg:tunit ~pos:tunit cns in
      let rvs = List.map (fun v -> Vrigid v) cnvars in
      let rhs = Tcvj (cns, rvs, Some cnloc) in
      make_err' env err (lhs, cploc) (rhs, cnloc)
    in
    raise (SubtypeError err)
  in
  let rec go (cp : _ Cons1.t loc) (cns : _ Cons1.t loc list) =
    let cp', cploc = cp in
    match cp', cns with
    | _, [] ->
       conflict ()
    | _, (Top,_)::_ -> ()
    | Func (pargs, pret), (Func (qargs, qret), _ as cn) :: _
         when List.compare_lengths pargs qargs = 0 ->
       List.combine qargs pargs
       |> List.iteri (fun i (a', a) -> neg cp cn (Func_arg i) a' a);
       pos cp cn Cons1.Func_res pret qret;
    | Record ({tag=ptag; _} as prec), (Record ({tag=qtag; _} as qrec), cnloc as cn):: _
         when Option.is_none qtag || Option.equal Cons1.Tag.equal ptag qtag ->
       begin match
         subtype_record_body ~env ~shape_a ~shape_b ~neg:(neg cp cn) ~pos:(pos cp cn) (prec,cploc) (qrec,cnloc)
       with
       | Ok () -> ()
       | Error err ->
          let err =
            match err with
            | Field_missing (name, ploc, nloc) ->
               make_err env (Field_missing name) (fst cp, ploc) (fst cn, nloc)
            | Field_extra (name, ploc, nloc) ->
               make_err env (Field_extra name) (fst cp, ploc) (fst cn, nloc)
          in
          raise (SubtypeError err)
       end
    | Variant_whole (tag, args), (Variant_whole (tag', args'), _ as cn) :: _
         when Nom_tag.equal_vtag tag tag' ->
       subtype_record_args ~neg:(neg cp cn) ~pos:(pos cp cn) args args'
    | Variant_whole (tag, args), ((Record {tag=Some (Named_tag (Variant_tag (s,_))); _}, _) :: _ as cns)
         when Nom_tag.equal_vtag tag s ->
       Cons1.expand_variant ~env tag args
       |> List.iter (fun case -> go (case,cploc) cns)
    | Record {tag=Some (Named_tag (Variant_tag (vtag,_))) as tag;_},
      (Variant_whole (vtag', args), cnloc) :: cns
        when Nom_tag.equal_vtag vtag vtag' ->
       go cp ((Record {tag; args; body=Fields.empty}, cnloc) :: cns)
    | _, ((Func _|Record _|Variant_whole _),_) :: cns ->
       go cp cns
  in
  go (cp,cploc) cns

let lower_contains_fv fv lower =
  List.exists (function
    | Lflexvar a -> equal_flexvar a fv
    | Lcons (Top, _) -> true
    | _ -> false) lower

let rigid_bound_simple env rv =
  Env.rigid_bound env rv
  |> Conses.map ~neg:(ntyp_to_fresh_flexvar ~simple:true env) ~pos:(ptyp_to_lower ~simple:true env)

let lower_of_rigid_bound env rv : lower =
  rigid_bound_simple env rv
  |> List.map (fun (c,cloc) -> Lcons (c, if cloc == Location.noloc then rv.loc else cloc))

let ptyp_of_rigid_bound env rv : ptyp =
  Tcvj (Env.rigid_bound env rv, [], Some rv.loc)

(* Check whether a flex-flex constraint α ≤ β is already present via an upper bound of α *)
let rec has_flex_upper (pv : flexvar) nv =
  pv == nv ||
  match pv.upper with
  | Uflexvar pv' -> has_flex_upper pv' nv
  | Ugen {conses=_; rvs=_; higher_fvs} -> List.memq nv higher_fvs
  | Utop -> false

type (+'neg,+'pos) upper_cons = ('neg,'pos) Cons1.t loc list * upper_rigvar list

let upper_find_rv rv (rvs : upper_rigvar list) =
  match
    rvs
    |> List.filter_map (function
      | urv when equal_rigvar rv urv.urv_var -> Some urv
      | _ -> None)
  with
  | _ :: _ :: _ -> intfail "duplicate RV in upper_cons"
  | [ds] -> Ok ds
  | [] -> Error ()


(* To preserve matchability, negative variables which are being duplicated need to be freshened *)
let rec freshen_neg_lower ~changes env lvl l =
  join_lower ~changes env lvl bottom l

and freshen_neg_flexvar ~changes env lvl v =
  let v' = fresh_flexvar lvl in
  subtype_flex_flex ~changes env v' v; v'

(* conses_a assumed matchable (unless must_freshen) and wf at lvl,
   conses_b may need hoisting *)
and meet_conses ~changes env lvl ~must_freshen (conses_a,loc_a) (conses_b,loc_b) =
  let match_shape = match_shape ~changes ~env in
  (* When a term from conses_a is duplicated (has meets with two conses_b),
     we need to freshen its matchable variables *)
  let neg ?(dup=false) x =
    let freshen l =
      if must_freshen || dup then freshen_neg_lower ~changes env lvl l else l
    in
    match (x : _ One_or_two.t) with
    | L x -> freshen x
    | R r -> join_lower ~changes env lvl bottom r
    | LR (x, r) -> join_lower ~changes env lvl (freshen x) r
  in
  let pos ?(dup=false) x =
    let freshen v =
      if must_freshen || dup then freshen_neg_flexvar ~changes env lvl v else v
    in
    match (x : _ One_or_two.t) with
    | L x -> freshen x
    | R r -> let v = fresh_flexvar lvl in r [Lflexvar v]; v
    | LR (v, r) -> let v = freshen v in r [Lflexvar v]; v
  in
  let meet_records ?(dup=false) ((a,a_loc) : _ Cons1.cons_record loc) ((b,b_loc) : _ Cons1.cons_record loc)
      : _ Cons1.cons_record loc =
    let dup, loc, tag, args =
      match a.tag, b.tag with
      | None, Some tag ->
         let dup = true in
         let args =
           let neg a = neg ~dup (R a) and pos a = pos ~dup (R a) in
           List.map (Cons1.Tyarg.map ~neg ~pos) b.args
         in
         dup, b_loc, Some tag, args

      | Some ta, Some tb ->
         assert (Cons1.Tag.equal ta tb);
         let neg a b = neg ~dup (LR (a, b)) and pos a b = pos ~dup (LR (a, b)) in
         dup, a_loc, Some ta, List.map2 (Cons1.Tyarg.zip ~neg ~pos) a.args b.args

      | tag, None ->
         assert (b.args = []);
         let neg a = neg ~dup (L a) and pos a = pos ~dup (L a) in
         dup, a_loc, tag, List.map (Cons1.Tyarg.map ~neg ~pos) a.args
    in
    let a_def = Cons1.record_def ~env ~shape:Type_shape.simple_neg ~loc:loc_a a in
    let b_def = Cons1.record_def ~env ~shape:match_shape ~loc:loc_b b in
    let body = Fields.meet ~pos:(pos ~dup) (a.body, a_def) (b.body, b_def) in
    { tag; args; body }, loc
  in
  conses_a |> List.concat_map (fun ((cons_a : _ Cons1.t), cons_a_loc) ->
    conses_b |> List.concat_map (fun ((cons_b : _ Cons1.t), cons_b_loc) ->
      match cons_a, cons_b with
      | cons_a, Top ->
         [cons_a, cons_a_loc]
      | Top, cons_b ->
         [Cons1.map cons_b ~neg:(fun x -> neg (R x)) ~pos:(fun x -> pos (R x)), cons_b_loc]
      | (Record _ | Variant_whole _), Func _ | Func _, (Record _ | Variant_whole _) -> []

      | Func (args, _), Func (args', _) when List.compare_lengths args args' <> 0 -> []
      | Func (args, res), Func (args', res') ->
         let args = List.map2 (fun x y -> neg (LR (x,y))) args args' in
         let res = pos (LR (res, res')) in
         [Func (args, res), cons_a_loc]

      | Variant_whole (tag_a, args_a), Variant_whole (tag_b, args_b) ->
         if Nom_tag.equal_vtag tag_a tag_b then
           let neg a b = neg (LR (a, b)) and pos a b = pos (LR (a, b)) in
           [Variant_whole (tag_a, List.map2 (Cons1.Tyarg.zip ~neg ~pos) args_a args_b), cons_a_loc]
         else []
      | Variant_whole (tag_a, args_a), Record ({tag = Some (Named_tag (Variant_tag (tag_b, _))) as tag; _} as b)
           when Nom_tag.equal_vtag tag_a tag_b ->
         let a : _ Cons1.cons_record = {tag; args = args_a; body = Fields.empty} in
         let r, loc = meet_records ~dup:true (a, cons_a_loc) (b, cons_b_loc) in
         [Record r, loc]
      | Record ({tag = Some (Named_tag (Variant_tag (tag_a, _))) as tag;_} as a), Variant_whole (tag_b, args_b)
           when Nom_tag.equal_vtag tag_a tag_b ->
         let b : _ Cons1.cons_record = {tag; args=args_b; body=Fields.empty} in
         let r, loc = meet_records (a, cons_a_loc) (b, cons_b_loc) in
         [Record r, loc]
      | Record _, Variant_whole _ | Variant_whole _, Record _ ->
         []

      | Record {tag=Some a;_}, Record{tag=Some b;_} when not (Cons1.Tag.equal a b) -> []
      | Record a, Record b ->
         let r, loc = meet_records (a, cons_a_loc) (b, cons_b_loc) in
         [Record r, loc])),
  (if loc_a == Location.noloc then loc_b else loc_a)

and match_shape ~changes ~env : (lower, lower -> unit, lower, flexvar) Type_shape.t =
  { of_typ_pos = (fun ~env t -> fun l -> subtype_lu ~changes env l (ntyp_to_upper ~simple:false env t));
    of_typ_neg = (fun ~env t -> ptyp_to_lower ~simple:false env t);
    to_typ_pos = (fun l -> let v = fresh_flexvar (Env.level env) in l [Lflexvar v]; Tsimple v);
    to_typ_neg = (fun t -> Tsimple t) }

and match_sub ~changes ~env ~loc:cnloc (p : lower_part) ((cn_conses, cn_rvs) : (lower, lower -> unit) upper_cons) : unit =
  let match_shape = match_shape ~changes ~env in
  let cnvars () =
    cn_rvs |> List.filter_map (fun urv -> !(urv.urv_ordered))
  in
  if Conses.is_top cn_conses then ()
  else match p with
  | Lrigvar rv ->
     begin match upper_find_rv rv cn_rvs with
     | Ok urv ->
        if Option.is_none !(urv.urv_ordered) then begin
          (* FIXME: is recursion ever relevant here? *)
          fv_set_ordered ~changes urv rv;
          subtype_lu ~changes env
            [p]
            (Ugen {conses=urv.urv_conses; rvs=[]; higher_fvs=[]});
        end
     | Error () ->
        rigid_bound_simple env rv |> List.iter (fun l ->
          try
            subtype_conses env l (cn_conses, cnloc)
              ~cnvars:(cnvars ())
              ~shape_a:Type_shape.simple_pos
              ~shape_b:match_shape
              ~neg:(fun p n -> subtype_lu ~changes env p (Uflexvar n))
              ~pos:(fun p pr -> pr p)
          with SubtypeError err ->
            let lhs = tvar (Vrigid rv) in
            let located =
              match Env.rigid_bound env rv with
              | [Top, _] -> ((lhs, rv.loc), snd err.located)
              | _ -> err.located
            in
            raise (SubtypeError
               {err with located; lhs; err = Head Incompatible }))
     end

  | Lcons (cp, cploc) ->
     subtype_conses env (cp, cploc) (cn_conses, cnloc)
       ~cnvars:(cnvars ())
       ~shape_a:Type_shape.simple_pos
       ~shape_b:match_shape
       ~neg:(fun p n -> subtype_lu ~changes env p (Uflexvar n))
       ~pos:(fun p pr -> pr p)

  | Lflexvar pv ->
     let {conses = (conses,upper_loc); rvs; higher_fvs} =
       rotate_flex ~changes env pv in
     (* shallow scope check *)
     let cn_rvs = List.filter (fun v -> Env_level.extends v.urv_var.level pv.level) cn_rvs in
     (* extract common rigid variables *)
     let meet_common_rvs, rvs = rvs |> List.partition_map (fun rv_a ->
       match upper_find_rv rv_a.urv_var cn_rvs with
       | Ok rv_b ->
          let b_conses =
            let cons, loc = rv_b.urv_conses in
            Conses.map cons ~neg:id ~pos:(fun u -> fun l ->
              subtype_lu ~changes env l (Uflexvar u)), loc
          in
          let urv_conses =
            meet_conses ~changes env pv.level ~must_freshen:false
              rv_a.urv_conses b_conses
          in
          !(rv_a.urv_ordered) |> Option.iter (fun rv_a ->
            subtype_lu ~changes env
              [Lrigvar rv_a]
              (Ugen {conses=rv_b.urv_conses; rvs=[]; higher_fvs=[]}));
          Left { rv_a with urv_conses }
       | Error () ->
          Right rv_a)
     in
     let cn_rvs = List.filter (fun rv_b -> Result.is_error (upper_find_rv rv_b.urv_var meet_common_rvs)) cn_rvs in
     let meet_rvs_a =
       rvs |> List.map (fun rv_a ->
         let urv_conses =
           meet_conses ~changes env pv.level ~must_freshen:false
             rv_a.urv_conses (cn_conses,cnloc)
         in
         !(rv_a.urv_ordered) |> Option.iter (fun rv_a ->
           subtype_lu ~changes env
             [Lrigvar rv_a]
             (Ugen {conses=urv_conses; rvs=[]; higher_fvs=[]}); (* somewhat redundant *));
         { rv_a with urv_conses })
     in
     let meet_rvs_b =
       cn_rvs |> List.map (fun rv_b ->
         let b_conses =
           let cons, loc = rv_b.urv_conses in
           Conses.map cons ~neg:id ~pos:(fun u -> fun l ->
             subtype_lu ~changes env l (Uflexvar u)), loc
         in
         let urv_conses =
           meet_conses ~changes env pv.level ~must_freshen:true
             (conses, upper_loc)
             b_conses
         in
         (* Set urv_ordered to ref None, but we're about to compare with
            pv.lower so it might soon change *)
         { urv_var = rv_b.urv_var;
           urv_conses;
           urv_ordered = ref None })
     in
     let urv_not_bot = function
       | {urv_conses = ([],_); _} -> false
       | _ -> true
     in
     let meet_old_rvs = List.filter urv_not_bot (meet_common_rvs @ meet_rvs_a) in
     let meet_new_rvs = List.filter urv_not_bot meet_rvs_b in
     let meet_conses =
       meet_conses ~changes env pv.level ~must_freshen:(not (List.is_empty meet_new_rvs))
         (conses, upper_loc)
         (cn_conses, cnloc)
     in
     (* Format.printf "MSUB %a@." dump_ptyp (Tsimple (of_flexvar pv)); *)
     (* FIXME: better fixpoint check here *)
     wf_ntyp env (Tsimple pv);
     let newbound = Ugen {conses = meet_conses; rvs=meet_old_rvs @ meet_new_rvs; higher_fvs} in
     (* Format.printf "meet: %a / %a%!" (pp_upper ~flexvar:ignore ~env) newbound dump_ptyp (Tsimple [Lflexvar pv]); *)
     if fv_maybe_set_upper ~changes pv newbound then
       subtype_lu ~changes env pv.lower newbound;
     wf_ntyp env (Tsimple pv);
     ()

and subtype_lpu ~changes env (p : lower_part) (n : upper) =
  match n with
  | Utop -> ()
  | Ugen {conses=(conses,loc); rvs; higher_fvs} ->
     higher_fvs |> List.iter (fun nv -> subtype_lpu ~changes env p (Uflexvar nv));
     let conses =
       Conses.map conses ~neg:id ~pos:(fun n ->
         fun p -> subtype_lu ~changes env p (Uflexvar n))
     in
     match_sub ~changes ~env ~loc p (conses, rvs);
     ()
  | Uflexvar nv ->
     begin match p with
     | Lflexvar pv -> subtype_flex_flex ~changes env pv nv
     | p ->
        let lower = join_lower_part ~changes env nv.level nv.lower p in
        if fv_maybe_set_lower ~changes nv lower then
          subtype_lpu ~changes env p nv.upper
     end

and subtype_lu ~changes env (p : lower) (n : upper) =
  p |> List.iter (fun p -> subtype_lpu ~changes env p n)

and rotate_flex ~changes env (pv : flexvar) : upper_gen =
  match pv.upper with
  | Ugen c -> c
  | Utop ->
     let c = { conses = ([Top, Location.noloc], Location.noloc); rvs = []; higher_fvs = [] } in
     fv_set_upper ~changes pv (Ugen c);
     assert (equal_upper pv.upper (Ugen c));
     c
  | Uflexvar v' when Env_level.equal v'.level pv.level ->
     let c = { conses = ([Top, Location.noloc], Location.noloc); rvs = []; higher_fvs = [] } in
     fv_set_upper ~changes pv (Ugen c);
     noerror (fun () -> subtype_flex_flex ~changes env pv v'); (*FIXME: impl directly?*)
     (* upper may have changed, retry *)
     rotate_flex ~changes env pv
  | Uflexvar v' ->
     let c = { conses =([Top, Location.noloc], Location.noloc); rvs = []; higher_fvs = [v'] } in
     fv_set_upper ~changes pv (Ugen c);
     assert (equal_upper pv.upper (Ugen c));
     c

and subtype_flex_flex ~changes env pv nv =
  (* We can record pv <= nv either as an upper bound on pv or a lower bound on nv.
     If they are not at the same level, our choice is forced.
     Otherwise, make an upper bound on pv, unless that would:
       - give pv two upper bounds, or
       - create a cycle of upper bounds *)
  if has_flex_upper pv nv || lower_contains_fv pv nv.lower then ()
  else if Env_level.extends nv.level pv.level
     && not (has_flex_upper nv pv) (* avoid creating cycles *)
     && pv.upper = Utop then begin
    fv_set_upper ~changes pv (Uflexvar nv);
    subtype_lu ~changes env pv.lower (Uflexvar nv)
  end else begin
    let pv_upper = rotate_flex ~changes env pv in
    if Env_level.extends pv.level nv.level then begin
      fv_set_lower ~changes nv (join_lower_part ~changes env nv.level nv.lower (Lflexvar pv));
      subtype_lpu ~changes env (Lflexvar pv) nv.upper
    end else begin
      fv_set_upper ~changes pv (Ugen {pv_upper with higher_fvs = nv::pv_upper.higher_fvs});
      subtype_lu ~changes env pv.lower (Uflexvar nv)
    end
  end

and join_lower_part ~changes env level lower ty =
  let rec join_fv lower fv =
    match lower with
    | Lcons (Top, _) :: _ -> lower
    | Lflexvar fv' :: rest when equal_flexvar fv fv'
      (* alt: [has_flex_upper fv' fv] - is this better? *) ->
       Lflexvar fv :: rest
    | part :: rest -> part :: join_fv rest fv
    | [] ->
       let fv =
         if Env_level.extends fv.level level then fv
         else
           let fv' = fresh_flexvar level in
           noerror (fun () -> subtype_flex_flex ~changes env fv fv'); fv'
       in
       [Lflexvar fv]
  in
  let rec join_rv lower rv =
    match lower with
    | Lcons (Top, _) :: _ -> lower
    | Lrigvar rv' :: _ when equal_rigvar rv rv' -> lower
    | part :: rest -> part :: join_rv rest rv
    | [] ->
       assert (Env_level.extends rv.level level);
       [Lrigvar rv]
  in
  let rec join_cons lower ((cb, cb_loc) : _ Cons1.t loc) =
    let neg vl vr =
      noerror (fun () -> subtype_flex_flex ~changes env vl vr);
      vl
    in
    let pos a b = join_lower ~changes env level a b in
    match lower, cb with
    | _, Top -> [Lcons (Top, cb_loc)]
    | (Lflexvar _ | Lrigvar _) as part :: rest, cb -> part :: join_cons rest (cb, cb_loc)
    | Lcons (Top, _loc) :: _, _ -> lower
    | (Lcons (Func _, _loc) as part :: rest), (Record _ | Variant_whole _)
    | (Lcons ((Record _ | Variant_whole _), _loc) as part :: rest), Func _ ->
       part :: join_cons rest (cb, cb_loc)

    | Lcons (Func (a_args, _), _) as part :: rest, Func (b_args, _)
         when List.compare_lengths a_args b_args <> 0 ->
       part :: join_cons rest (cb, cb_loc)
    | Lcons (Func (a_args, a_ret), a_loc) :: rest, Func (b_args, b_ret) ->
       let args = List.map2 neg a_args b_args in
       let ret = pos a_ret b_ret in
       Lcons (Func (args, ret), a_loc) :: rest

    | Lcons (Record {tag=Some a;_}, _) as part :: rest, Record {tag=Some b;_}
         when not (Cons1.Tag.equal a b) ->
       part :: join_cons rest (cb, cb_loc)
    | Lcons (Record a, a_loc) :: rest, Record b ->
       let shape = Type_shape.simple_pos in
       let a, b, rest =
         match a.tag, b.tag with
         | Some _, Some _
         | None, None ->
            a, b, rest
         | None, Some _ ->
            let b = Cons1.drop_record_tag ~shape env b in
            a, b, rest
         | Some _, None ->
            let a = Cons1.drop_record_tag ~shape env a in
            (* These were separate in a but must now be combined *)
            let records, nonrecords =
              rest |> List.partition_map (function
                | Lcons (Record _ as r, r_loc) -> Left (r, r_loc)
                | x -> Right x)
            in
            let a = List.fold_left join_cons [Lcons (Record a,a_loc)] records in
            let a = match a with [Lcons (Record r,_loc)] -> r | _ -> intfail "nonrecord after join" in
            a, b, nonrecords
       in
       let a_def = Cons1.record_def ~env ~shape ~loc:a_loc a in
       let b_def = Cons1.record_def ~env ~shape ~loc:cb_loc b in
       let r =
         Cons1.Record {tag = a.tag;
                       args = List.map2 (Cons1.Tyarg.zip ~neg ~pos) a.args b.args;
                       body = Fields.join ~pos (a.body, a_def) (b.body, b_def)}
       in
       Lcons (r, a_loc) :: rest

    | Lcons (Variant_whole (a_tag,a_args), a_loc) as part :: rest, Variant_whole(b_tag,b_args) ->
       if Nom_tag.equal_vtag a_tag b_tag then
         let args = List.map2 (Cons1.Tyarg.zip ~neg ~pos) a_args b_args in
         Lcons (Variant_whole(a_tag, args), a_loc) :: rest
       else
         part :: join_cons rest (cb, cb_loc)

    | Lcons (Variant_whole (a_tag,a_args), a_loc) :: rest, Record{tag=Some (Named_tag (Variant_tag (b_tag, _))); _}
         when Nom_tag.equal_vtag a_tag b_tag ->
       (* FIXME: it would be neat to skip expansion in some cases.
          Requires knowledge of per-case variance information - is this worth computing in general?
          (Easy case: no parameters) *)
       let exp =
         Cons1.expand_variant ~env a_tag a_args
         |> List.map (fun c -> Lcons (c, a_loc))
       in
       join_cons (exp @ rest) (cb, cb_loc)
    | (Lcons (Record{tag=Some (Named_tag (Variant_tag (a_tag, _))); _}, _) :: _) as orig, Variant_whole (b_tag,b_args)
         when Nom_tag.equal_vtag a_tag b_tag ->
       (* FIXME: skip expansion as per above? *)
       let exp = Cons1.expand_variant ~env b_tag b_args in
       List.fold_left (fun acc cons -> join_cons acc (cons, cb_loc)) orig exp
    | (Lcons (Variant_whole _, _loc) as part) :: rest, Record _
    | (Lcons (Record _, _loc) as part) :: rest, Variant_whole _ ->
       part :: join_cons rest (cb, cb_loc)


    | [], cb ->
       let cons =
         Cons1.map cb
           ~neg:(freshen_neg_flexvar ~changes env level)
           ~pos:(freshen_neg_lower ~changes env level)
       in
       [Lcons (cons, cb_loc)]
  in

  match ty with
  | Lflexvar fv -> join_fv lower fv
  | Lrigvar rv ->
     if Env_level.extends rv.level level
     then join_rv lower rv
     else join_lower ~changes env level lower (lower_of_rigid_bound env rv)
  | Lcons cb -> join_cons lower cb

and join_lower ~changes env level lower (ty : lower) =
  List.fold_left (join_lower_part ~changes env level) lower ty

let check_simple t =
  let rec aux = function
    | Tsimple _ -> ()
    | Tpoly _ -> raise Exit
    | Tcvj (_, _ :: _, _cloc) -> () (* by invariant *)
    | Tcvj (c, [], _cloc) ->
       ignore (Conses.map c ~neg:aux ~pos:aux)
  in
  match aux t with
  | () -> true
  | exception Exit -> false

let upper_is_bot = function
  | Ugen {conses=([],_); rvs=[]; higher_fvs=_} -> true
  | _ -> false


(*
 * Subtyping on typs (polymorphism)
 *)

let enter_rigid env vars rig_names =
  let level = Env_level.extend (Env.level env) in
  let getrv (conses, vars, loc) vars' =
    let vars = vars @ (List.map (fun (var,loc) -> Vrigid {level;loc;var}) vars') in
    Tcvj (conses, vars, loc)
  in
  let openrig t = open_typ ~neg:getrv ~pos:getrv 0 t in
  let rig_defns = IArray.map (fun (name, b) ->
     let upper = Option.map openrig b in
     match upper with
     | None ->
        { name; upper = [Top, Location.noloc] }
     | Some t when is_ttop t ->
        { name; upper = [Top, Location.noloc] }
     | Some (Tcvj (conses, [], _loc)) ->
        { name; upper = conses }
     | Some _ ->
       (* FIXME: can you actually hit this?
          Try with a higher-rank type where the outer rank gets instantiated.
          Maybe change the type of the upper bound in parsed types.
          (to reflect its Tconsness)*)
        assert false)
     vars
  in
  let env = Env.extend_types env ~level ~rig_names ~rig_defns in
  env, openrig, openrig

let rec subtype_exn env (p : ptyp) (n : ntyp) =
  (* Format.printf "%a <= %a\n" dump_ptyp p pp_ntyp n; *)
  wf_ptyp env p; wf_ntyp env n;
  match p, n with
  | _, t when is_ttop t -> ()
  | t, _ when is_tbot t -> ()
  | Tcvj (cp,vp,_ploc), Tcvj (cns,vn,nloc) ->
     cp |> List.iter (fun cp ->
       subtype_conses env
         ~cnvars:(List.map as_rigvar vn)
         ~shape_a:Type_shape.gen_pos
         ~shape_b:Type_shape.gen_neg
         ~neg:(subtype_exn env) ~pos:(subtype_exn env)
         cp (cns,Option.value nloc ~default:(Location.fixme "subtype_exn")));
     vp |> List.iter (fun vp ->
       if not (List.exists (equal_typ_var vp) vn) then
         subtype_lu ~changes:(ref []) env [Lrigvar (as_rigvar vp)] (ntyp_to_upper ~simple:false env n));
  | p, Tpoly {vars; body} ->
     let orig_env = env in
     let env, open_rvars, _ = enter_rigid env vars SymMap.empty in
     let body = open_rvars body in
     (try subtype_exn env p body
      with SubtypeError err ->
        raise (SubtypeError (close_err_rigid ~orig_env ~env vars err)))
  | Tpoly {vars; body}, n ->
     let body = instantiate_flex env vars body in
     subtype_exn env body n; ()
  | ((Tsimple _ | Tcvj _) as p), ((Tsimple _ | Tcvj _) as n) ->
     let u = ntyp_to_upper ~simple:false env n in
     subtype_lu ~changes:(ref []) env (ptyp_to_lower ~simple:false env p) u;
     wf_ptyp env p; wf_ntyp env n;
     ()

let subtype env p n =
  (* FIXME: revert changes on failure? *)
  match subtype_exn env p n with
  | exception SubtypeError e ->
     assert (fst e.env == env);
     Error e
  | () -> Ok ()

(* FIXME: rank1 joins maybe? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  match p, q with
  | p, q when is_tbot p -> q
  | p, q when is_tbot q -> p
  | p, _ when is_ttop p -> p
  | _, q when is_ttop q -> q
  | Tcvj (cons_p, vars_p, loc_p), Tcvj (cons_q, vars_q, loc_q)
       when
         cons_p |> List.for_all (fun (p,_) ->
           cons_q |> List.for_all (fun (q,_) ->
             Cons1.incomparable_head p q))
    ->
     let vars =
       vars_p @ List.filter (fun v -> not (List.exists (equal_typ_var v) vars_p)) vars_q
     in
     Tcvj(cons_p @ cons_q,
          vars,
          (match loc_p with Some _ -> loc_p | _ -> loc_q))
  | p, q ->
    let p = ptyp_to_lower ~simple:false env p in
    let q = ptyp_to_lower ~simple:false env q in
    let changes = ref [] in
    (* Must start with bottom to ensure correct freshening *)
    let r = bottom in
    let r = join_lower ~changes env (Env.level env) r p in
    let r = join_lower ~changes env (Env.level env) r q in
    Tsimple r

(* FIXME: is this ever needed in nontrivial ways? *)
let meet_ntyp env (p : ntyp) (q : ntyp) : ntyp =
  if is_ttop p then q
  else if is_ttop q then p
  else
     let v = fresh_flexvar (Env.level env) in
     subtype_lpu ~changes:(ref []) env (Lflexvar v) (ntyp_to_upper ~simple:false env p);
     subtype_lpu ~changes:(ref []) env (Lflexvar v) (ntyp_to_upper ~simple:false env q);
     Tsimple v

let rec match_ptyp ~loc env (p : ptyp) (heads : (ntyp->unit, ptyp->unit) Cons1.t loc list) =
  let match_shape : (ntyp->unit, ptyp->unit, lower, flexvar) Type_shape.t =
    { of_typ_pos = (fun ~env (n:ntyp) -> fun p -> subtype_exn env p n);
      of_typ_neg = (fun ~env (p:ptyp) -> fun n -> subtype_exn env p n);
      to_typ_pos = (fun t -> let v = fresh_flexvar (Env.level env) in t (Tsimple [Lflexvar v]); Tsimple v);
      to_typ_neg = (fun t -> let v = fresh_flexvar (Env.level env) in t (Tsimple v); Tsimple [Lflexvar v])}
  in
  match p with
  (* FIXME: Can/should this work with vars too? *)
  | Tcvj (conses, [], _jloc) ->
     conses |> List.iter (fun c ->
       subtype_conses env c (heads, loc)
         ~cnvars:[]
         ~shape_a:Type_shape.gen_pos
         ~shape_b:match_shape
         ~neg:(fun v t -> v t)
         ~pos:(fun t v -> v t))
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_ptyp ~loc env body heads
  | t ->
     let instneg v =
       let fv = fresh_flexvar (Env.level env) in
       v (Tsimple fv);
       [Lflexvar fv] in
     let shead = Conses.map heads ~neg:instneg ~pos:(fun v -> fun p -> v (Tsimple p)) in
     ptyp_to_lower ~simple:false env t
     |> List.iter (fun l -> match_sub ~changes:(ref []) ~env ~loc l (shead,[]))

let match_ptyp ~loc env ty heads =
  let heads =
    Conses.map heads
      ~neg:(fun r -> fun t -> r := meet_ntyp env !r t)
      ~pos:(fun r -> fun t -> r := join_ptyp env !r t)
  in
  match match_ptyp ~loc env ty heads with
  | () -> Ok ()
  | exception (SubtypeError e) ->
     assert (fst e.env == env);
     Error e

(*
 * Generalisation
 *)

(* Returns true only if a <= b
   Not complete, never changes anything.
   Used only for optimisations, to avoid generalising a when x <= a <= x.
   Not a bug if it spuriously returns false sometimes (but leads to uglier types) *)
(* FIXME: can this diverge? *)
let rec clearly_subtype env (a : flexvar) (b : lower) : bool =
  lower_contains_fv a b ||
  match a.upper with
  | Utop -> false
  | Uflexvar a -> clearly_subtype env a b
  | Ugen {higher_fvs = fvs; _} when
     List.exists (fun a' -> clearly_subtype env a' b) fvs -> true
  | Ugen {conses=(conses,_); rvs; higher_fvs=_} ->
     let b_cons = b |> List.filter_map (function Lcons b -> Some b | _ -> None) in
     let sub a b = if not (clearly_subtype env a b) then raise Exit in
     (conses |> List.for_all (fun a ->
     match subtype_conses ~cnvars:[] env ~shape_a:Type_shape.simple_neg ~shape_b:Type_shape.simple_pos ~neg:sub ~pos:sub a (b_cons,Location.noloc) with
     | () -> true
     | exception (Exit | SubtypeError _) -> false))
    &&
    (rvs |> List.for_all (fun {urv_var=rv; urv_conses=_; urv_ordered=_} ->
      (* It is correct to ignore urv_conses here,
         since LHS is <= rv regardless *)
      b |> List.exists (function
        | Lrigvar rv' ->
           equal_rigvar rv rv'
        | _ -> false)))

let rec clearly_subtype_typ env (a : _ typ) (b : _ typ) : bool =
  match a, b with
  | Tcvj (cons_a, vars_a, _), Tcvj (cons_b, vars_b, _) ->
     vars_a |> List.for_all (fun a -> vars_b |> List.exists (equal_typ_var a))
     &&
     cons_a |> List.for_all (fun a ->
       let sub a b = if not (clearly_subtype_typ env a b) then raise Exit in
       match subtype_conses ~cnvars:[] env ~shape_a:Type_shape.gen_neg ~shape_b:Type_shape.gen_pos ~neg:sub ~pos:sub a (cons_b,Location.noloc) with
       | () -> true
       | exception (Exit | SubtypeError _) -> false)
  | (Tsimple _ | Tcvj _), (Tsimple _ | Tcvj _) ->
     clearly_subtype env
       (ntyp_to_fresh_flexvar ~simple:false env a)
       (ptyp_to_lower ~simple:false env b)
  | Tpoly {vars=vars_a; body=a}, Tpoly {vars=vars_b; body=b}
       when IArray.length vars_a = IArray.length vars_b ->
     (* Try pairing up the variables directly *)
     IArray.for_all2
       (fun x y -> match x, y with
        | (_,None), _  -> true
        | _, (_, None) -> false
        | (_,Some a), (_,Some b) -> clearly_subtype_typ env b a)
       vars_a
       vars_b
     &&
     (* entering vars_b would be more precise but it's the wrong type *)
     (let env, open_rvars, open_rvars' = enter_rigid env vars_a SymMap.empty in
      clearly_subtype_typ env (open_rvars a) (open_rvars' b))
  | Tpoly _, _ | _, Tpoly _ ->
     false

let rec clearly_subtype_bounds env (a : (unit,unit) typ) (b : (unit,unit) typ) : bool =
  match a, b with
  | _, b when is_ttop b -> true
  | a, _ when is_tbot a -> true
  | Tcvj (cons_a, vars_a, _loc_a), Tcvj (cons_b, vars_b, _loc_b) ->
     vars_a |> List.for_all (fun a -> vars_b |> List.exists (equal_typ_var a))
     &&
     cons_a |> List.for_all (fun a ->
       let sub a b = if not (clearly_subtype_bounds env a b) then raise Exit in
       match subtype_conses ~cnvars:[] env ~shape_a:Type_shape.gen_unit ~shape_b:Type_shape.gen_unit ~neg:sub ~pos:sub a (cons_b,Location.noloc) with
       | () -> true
       | exception (Exit | SubtypeError _) -> false)
  | Tpoly _, _ | _, Tpoly _ -> intfail "Tpoly in rv bounds"
  | Tsimple (), _ | _, Tsimple () -> false

(* FIXME: bit weird... There must be a better representation for bvars here *)

type genvar =
  | Gen_flex of ntyp
  | Gen_rigid of rigvar

(*

design:
  switch to a different mode for subst'ing in elaborations
  in elab mode:
    1. don't worry about contravariant joins in substn_upper
    2. if keeping a var that occurs negatively, always expand (even at neg occs)
    3. if bivariant vars don't have a bound ix by now, don't make one (expand & drop)

  3 amounts to replacing vars with their lower bound if not used in gen type.
  Two other classes of vars could in theory be dropped:
    - vars used positively in gen type and negatively only in elab
    - vars used negatively in gen type and positively only in elab

  FIXME: 1 is not implemented yet (requires testing)
 *)

let is_visited_pos visit fv =
  match fv.gen with
  | Not_generalising -> assert false
  | Generalising {visit={pos;_};_} ->
     assert (pos land 1 = 0);
     pos = visit

let is_visited_neg visit fv =
  match fv.gen with
  | Not_generalising -> assert false
  | Generalising {visit={neg;_};_} ->
     assert (neg land 1 = 0);
     neg = visit

(* Invariants after expansion:
   - All flexvars are joined with their lower bounds
   - All +-reachable flexvars are rotated
   - All --reachable flexvars have at most one upper bound
      (not counting UBvar upper bounds at higher levels)
   (Only applied to flexvars at the current level) *)

let remove_flexvar fv lower =
  List.filter (function Lflexvar a when equal_flexvar fv a -> false | _ -> true) lower

let rec expand_lower visit ~changes ?(vexpand=[]) env orig_lower =
  let level = Env.level env in
  let lower =
    orig_lower |> List.map (function
      | Lflexvar pv when Env_level.equal pv.level level ->
          fv_gen_visit_pos env visit pv (function
            | Recursive_visit ->
               (* recursive occurrences are fine if not under a constructor *)
               if not (List.memq pv vexpand)
               then unimp "positive recursion on flexvars"
            | First_visit ->
               let _ = rotate_flex ~changes env pv in
               (* Add pv to expand so we ignore it if seen before the next ctor *)
               let lower = expand_lower visit ~changes ~vexpand:(pv::vexpand) env pv.lower in
               ignore (fv_maybe_set_lower ~changes pv (remove_flexvar pv lower)));
          Lflexvar pv
      | Lflexvar _ | Lrigvar _ as l -> l
      | Lcons (c, cloc) ->
         Lcons (Cons1.map c ~neg:(expand_fv_neg visit ~changes env) ~pos:(expand_lower visit ~changes env), cloc))
  in
  let lower =
    List.fold_left
      (fun acc l ->
        match l with
        | Lflexvar fv when Env_level.equal fv.level level ->
           join_lower ~changes env level acc fv.lower
        | _ -> acc)
      lower
      lower
  in
  let lower_rest, fv_here =
    lower |> List.partition_map (function
      | Lflexvar fv when Env_level.equal fv.level level -> Right fv
      | l -> Left l)
  in
  let fv_here =
    fv_here
    |> List.filter (fun fv -> not (clearly_subtype env fv lower_rest))
    |> List.map (fun x -> Lflexvar x)
  in
  lower_rest @ fv_here


and expand_fv_neg visit ~changes env nv =
  fv_gen_visit_neg env visit nv (function
    | Recursive_visit ->
       unimp "neg cycle on recursive flexvar"
    | First_visit ->
       match nv.upper with
       | Utop -> ()
       | Uflexvar v when Env_level.equal nv.level v.level ->
          ignore (expand_fv_neg visit ~changes env v)
       | _ ->
          let change = ref false in
          let map_conses c =
            Conses.map c
              ~neg:(fun x ->
                   let x' = expand_lower visit ~changes env x in
                   if not (equal_lower x x') then change := true;
                   x')
              ~pos:(expand_fv_neg visit ~changes env)
          in
          let { conses = (conses,consloc); rvs; higher_fvs } =
            rotate_flex ~changes env nv in
          let conses = map_conses conses in
          let rvs =
            rvs |> List.map (function
              | urv when Option.is_some !(urv.urv_ordered) -> urv
              | { urv_conses = (c,loc); _ } as urv ->
                 { urv with urv_conses = map_conses c, loc })
          in
          (* FIXME change tracking *)
          if true || !change then ignore (fv_maybe_set_upper ~changes nv (Ugen {conses = (conses, consloc); rvs; higher_fvs}))
  );
  nv

(* FIXME: does not yet detect the creation of contravariant joins
   during promotion. These arise (only?) during promotions with
   rigvars at the current level. *)

type ('n, 'p) promotion_policy =
  | Policy_hoist : env -> (flexvar, lower) promotion_policy
  | Policy_generalise : Location.t -> (zero, zero) promotion_policy

type ('n, 'p) promote_info = {
  visit: int;
  bvars: genvar Vector.t;
  env: env;
  level: Env_level.t;
  index: int;
  mode: [`Poly | `Elab];
  policy : ('n, 'p) promotion_policy;
}

let promote_rigvar _s (rv : rigvar) = Vrigid rv

type ('n, 'p) promote_flexvar_result =
  | Generalised : int -> (zero, zero) promote_flexvar_result
  | Hoisted : flexvar -> (flexvar, lower) promote_flexvar_result

type promvar =
  | Prom_var of typ_var
  | Prom_hoist of flexvar
  | Prom_drop

let trim_overrides ~env xs =
  xs |> List.map (function
    | Cons1.Record r, loc ->
       let def = Cons1.record_def ~env ~shape:Type_shape.gen ~loc r in
       let no _ _ = false in
       let eq = Fields.equal_field_desc (Typedefs.equal_typ ~neg:no ~pos:no) in
       let body = Fields.filteri r.body ~f:(fun fn x -> not (eq x (def fn))) in
       Cons1.Record {r with body}, loc
    | cons -> cons)

let rec promote_lower :
  type n p . (n, p) promote_info -> lower -> (n, p) typ =
  fun s lower ->
  let conses, vars =
    lower |> List.partition_map (function
      | Lcons (c, cloc) ->
         Left (Cons1.map ~neg:(promote_fv_neg s) ~pos:(promote_lower s) c, cloc)
      | Lrigvar rv ->
         Right (Prom_var (promote_rigvar s rv))
      | Lflexvar fv ->
         begin match promote_flexvar s fv with
         | None -> Right Prom_drop
         | Some r ->
            match s.policy with
            | Policy_generalise loc ->
               let Generalised var = r in
               Right (Prom_var (Vrigid {level=s.level; var; loc}))
            | Policy_hoist _env ->
               let Hoisted fv = r in
               Right (Prom_hoist fv)
         end)
  in
  let vars, vflex =
    vars
    |> List.filter_map (function
      | Prom_drop -> None
      | Prom_var v -> Some (Either.Left v)
      | Prom_hoist fv -> Some (Either.Right fv))
    |> List.partition_map id
  in
  let conses = trim_overrides ~env:s.env conses in
  let ty = Tcvj(conses, List.sort_uniq compare_typ_var vars, None) in
  match vflex with
  | [] -> ty
  | vflex ->
     match s.policy with
     | Policy_generalise _ -> assert false
     | Policy_hoist henv ->
        let ty =
          (* FIXME: rearrange *)
          let _ =
            let fail (_,_,loc) = raise (CloseError (Join_bad_scoping, loc)) in
            close_typ ~neg:fail ~pos:fail s.level 0 ty
          in
          ptyp_to_lower ~simple:true henv ty
          @ List.map (fun v -> Lflexvar v) vflex
        in
        Tsimple ty

and promote_fv_neg :
  type n p . (n, p) promote_info -> flexvar -> (p, n) typ =
  fun s nv ->
  match promote_flexvar s nv, s.policy with
  | None, _ ->
     (* substitute away the variable *)
     let vars, ty = promote_upper s nv in
     assert (vars = []);
     ty
  | Some (Generalised var), Policy_generalise loc ->
     let v = Vrigid {level=s.level; var; loc} in
     assert (is_visited_pos s.visit nv);
     begin match s.mode with
     | `Poly -> tvar v
     | `Elab ->
        (* Here a positive type is used as negative, but only when:
           - Elab, so placement of rigid variables doesn't matter
           - Policy_generalise, so there are no flexible variables *)
        (* FIXME ugly match *)
        begin match promote_lower s nv.lower with
        | Tcvj (cons, vars, loc) ->
           Tcvj (cons, vars @ [v], loc)
        | _ -> assert false
        end
     end
  | Some (Hoisted v), Policy_hoist hoist_env ->
     assert (Env_level.extends v.level (Env.level hoist_env));
     Tsimple v

and promote_upper :
  type n p . (n, p) promote_info -> flexvar -> flexvar list * (p,n) typ =
  fun s fv ->
  match fv.upper with
  | Uflexvar v when Env_level.equal v.level s.level ->
     assert (not (is_visited_pos s.visit fv));
     [], promote_fv_neg s v
  | u ->
     let conses, loc, rvs, vars =
       match u with
       | Utop -> [Cons1.Top, Location.noloc], Location.noloc, [], []
       | Uflexvar v -> [Cons1.Top, Location.noloc], Location.noloc, [], [v]
       | Ugen {conses=(conses,loc);rvs;higher_fvs} -> conses, loc, rvs, higher_fvs
     in
     let conses =
       conses
       |> Conses.map ~neg:(promote_lower s) ~pos:(promote_fv_neg s)
       |> trim_overrides ~env:s.env
     in
     (* conses are expanded if urv_ordered is false! *)
     let rigvars =
       (* FIXME: is it better to error or just drop RVs here? *)
       if not (List.is_empty conses) then []
       else rvs |> List.filter_map (function
         | rv when Option.is_some !(rv.urv_ordered) -> Some (promote_rigvar s rv.urv_var)
         | { urv_var = rv; urv_conses = (conses, loc); urv_ordered = _ } ->
            (* rv & conses = rv if rv <= conses
               Otherwise, set to bottom (sound but not principal!)*)
            let ignore_simple t = map_typ_1 ~neg:ignore ~pos:ignore ~index:0 t in
            let bound = ptyp_of_rigid_bound s.env rv in
            let conses = Conses.map conses ~neg:(promote_lower s) ~pos:(promote_fv_neg s) in
            let cons_ty = Tcvj (conses, [], Some loc) in
            if clearly_subtype_bounds s.env (ignore_simple bound) (ignore_simple cons_ty)
            then Some (promote_rigvar s rv)
            else None)
     in
     vars, Tcvj (conses, rigvars, Some loc)


and promote_flexvar :
  type n p . (n, p) promote_info -> flexvar -> (n, p) promote_flexvar_result option =
  fun s fv ->
  if not (Env_level.equal fv.level s.level) then
    match s.policy with
    | Policy_hoist hoist_env ->
       assert (Env_level.extends fv.level (Env.level hoist_env));
       Some (Hoisted fv)
    | Policy_generalise _ ->
       intfail "Flexible variable found during generalisation" (* MonoLocalBinds *)
  else begin
  assert (Env_level.equal fv.level s.level);
  match fv.gen with
  | Not_generalising -> assert false
  | Generalising gen ->
     let upper_requires_hoist = function
       | Uflexvar v when Env_level.equal v.level s.level -> false
       | Utop | Ugen {conses=_; rvs=_; higher_fvs=[]} -> false
       | _ -> true
     in
     if not (gen.visit.neg = s.visit && (gen.visit.pos = s.visit || upper_requires_hoist fv.upper))
     then None
     else match gen.bound_var with
     | Computing_bound ->
        (* FIXME: detect all recursion cases during expand so this can go away *)
        unimp "flexvar recursive in own bound"
     | Generalised var ->
        (match s.policy with Policy_generalise _ -> Some (Generalised var) | _ -> assert false)
     | Kept fv ->
        (match s.policy with Policy_hoist _ -> Some (Hoisted fv) | _ -> assert false)
     | Replace_with_rigid _ ->
        assert false
     | No_var_chosen ->
        gen.bound_var <- Computing_bound;
        let bv : flexvar_gen_status =
          assert (is_visited_pos s.visit fv || upper_requires_hoist fv.upper);
          let vars, upper = promote_upper s fv in
          match s.policy with
          | Policy_generalise _ ->
            assert (vars = []); (* since visited_pos *)
            let n = Vector.push s.bvars (Gen_flex (gen_zero upper)) in
            Generalised n
          | Policy_hoist hoist_env ->
              (* FIXME: surely I need to consider fv.lower as well? *)
            let h = fresh_flexvar (Env.level hoist_env) in
            Result.get_ok
              (subtype hoist_env (Tsimple [Lflexvar h]) upper);
            vars |> List.iter (fun var' ->
              Result.get_ok
                (subtype hoist_env (Tsimple [Lflexvar h]) (Tsimple var')));
            Kept h
        in
        gen.bound_var <- bv;
        (* FIXME refactor *)
        promote_flexvar s fv
  end

let fixpoint_iters = ref 0
let log_changes = ref false
let verbose_types = match Sys.getenv "VERBOSE_TYPES" with _ -> true | exception Not_found -> false

module Promotion (P : sig
  type t
  val map :
    neg:(mode:[ `Elab | `Poly ] ->
         ext:int list -> ntyp -> ntyp) ->
    pos:(mode:[ `Elab | `Poly ] ->
         ext:int list -> ptyp -> ptyp) ->
    t -> t
end) = struct

let promote_exn ~policy ~rigvars ~env (ty : P.t) : _ * P.t =
  (* Format.printf "ELAB %a{\n%a}@." dump_ptyp orig_ty pp_elab_req erq; *)
  let rec fixpoint visit (prev_ty : P.t) =
    (* if verbose_types then Format.printf "FIX: %a" dump_ptyp prev_ty; *)
    if visit > 99 then intfail "looping?";
    let changes = ref [] in
    let neg_simple t =
      expand_fv_neg visit ~changes env t
    in
    let pos_simple t =
      let t' = expand_lower visit ~changes env t in
      if not (equal_lower t t') then
        changes := Change_expanded_mark :: !changes;
      t'
    in
    let neg ~mode:_ ~ext t = map_typ_1 ~index:(List.length ext) ~neg:pos_simple ~pos:neg_simple t in
    let pos ~mode:_ ~ext t = map_typ_1 ~index:(List.length ext) ~neg:neg_simple ~pos:pos_simple t in
    let ty = P.map ~neg ~pos prev_ty in
    if !log_changes || visit > 90 then Format.printf "changed: %a\n\n%!" pp_changes !changes;
    if !changes = [] then
      (visit, ty)
    else
      (incr fixpoint_iters; fixpoint (visit+2) ty) in
  let visit, ty = fixpoint 2 ty in
  (* Format.printf "ELAB2 %a{\n%a}@." dump_ptyp ty pp_elab_req erq; *)
  let bvars = Vector.create () in
  rigvars |> IArray.iteri (fun var ((_,loc),_) -> ignore (Vector.push bvars (Gen_rigid {loc;var;level=Env.level env})));
  let promote (type p) (type n) (policy : (n,p) promotion_policy) =
    let s_base = { visit; bvars; env; level = Env.level env; mode = `Poly; index = -1; policy } in
    let neg_simple ~mode ~index t : ntyp =
      let t = promote_fv_neg {s_base with mode; index} t in
      match policy with Policy_generalise _ -> gen_zero t | Policy_hoist _ -> t
    in
    let pos_simple ~mode ~index (t : lower) : ptyp =
      let t = promote_lower {s_base with mode; index} t in
      match policy with Policy_generalise _ -> gen_zero t | Policy_hoist _ -> t
    in
    let trim ~index:_ c = trim_overrides ~env c in
    P.map ty
      ~neg:(fun ~mode ~ext t ->
        let index = List.length ext in
        map_typ_0
          ~neg:(pos_simple ~mode) ~pos:(neg_simple ~mode)
          ~neg_cons:trim ~pos_cons:trim
          ~index t)
      ~pos:(fun ~mode ~ext t ->
        let index = List.length ext in
        map_typ_0
          ~neg:(neg_simple ~mode) ~pos:(pos_simple ~mode)
          ~neg_cons:trim ~pos_cons:trim
          ~index t)
  in
  (* Format.printf "ELAB3 %a{\n%a}@." dump_ptyp ty pp_elab_req erq; *)
  let ty =
    match policy with
    | `Generalise loc -> promote (Policy_generalise loc)
    | `Hoist env -> promote (Policy_hoist env)
  in
  let bvars, ty =
    let neg ~mode ~ext t =
      let index = List.length ext in
      match mode with
        | `Elab -> close_typ ~neg:ignore ~pos:ignore (Env.level env) index t
        | `Poly -> close_typ ~neg:close_poly_pos ~pos:close_poly_neg (Env.level env) index t
    in
    let pos ~mode ~ext t =
      let index = List.length ext in
      match mode with
      | `Elab -> close_typ ~neg:ignore ~pos:ignore (Env.level env) index t
      | `Poly -> close_typ ~neg:close_poly_neg ~pos:close_poly_pos (Env.level env) index t
    in
    let bvars = Vector.to_array bvars in
    let bvars = bvars |> Array.map (function
      | Gen_rigid _ as x -> x
      | Gen_flex b -> Gen_flex (neg ~mode:`Poly ~ext:[] b)) in
    bvars, P.map ty ~neg ~pos
  in
  let bounds =
    let next_name = ref 0 in
    let rec mkname () =
      let n = !next_name in
      incr next_name;
      let name = match n with
        | n when n < 26 -> Printf.sprintf "%c" (Char.chr (Char.code 'a' + n))
        | n -> Printf.sprintf "t_%d" (n-26) in
      (* NB: look up env, to ensure no collisions with rigvars *)
      match Typedefs.env_lookup_type_var env Location.noloc name with
      | None -> name, Location.noloc
      | Some _ -> mkname () in
    bvars
    |> Array.map (function
      | Gen_rigid rv -> IArray.get rigvars rv.var
      | Gen_flex r when is_ttop r -> mkname (), None
      | Gen_flex r -> mkname (), Some r)
    |> IArray.of_array
  in
  bounds, ty

end
