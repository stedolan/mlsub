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

let close_poly_pos ((_,_,loc) as ty) =
  if not (is_locally_closed 0 (Tcvj ty)) then
    raise (CloseError (Join_bad_scoping, loc))

let close_typ_poly_exn ~ispos lvl ty =
  if ispos
  then close_typ ~neg:close_poly_neg ~pos:close_poly_pos lvl 0 ty
  else close_typ ~neg:close_poly_pos ~pos:close_poly_neg lvl 0 ty


let tcons_head (c, loc) =
  let tunit _ = Tsimple () in
  tcons (Cons1.map ~neg:tunit ~pos:tunit c, loc)

type conflict =
  | Head of Cons1.head_conflict
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

let make_head_err env err (lhs, cploc) (cn, cnloc) =
  let err = Head err in
  let conses, rvs =
    let tunit _ = Tsimple () in
    cn |> List.partition_map (function
      | Ucons c -> Left (Cons1.map ~neg:tunit ~pos:tunit c, cnloc)
      | Urigvar (rv, ds) -> Right (rv, ds))
  in
  let rvs =
    rvs |> List.filter_map (function
      | (rv, []) -> Some (Vrigid rv)
      | (_rv, _ :: _) -> None (* ignore if delayed constraint. (FIXME?) *))
  in
  let rhs = Tcvj (conses, rvs, Some cnloc) in
  make_err' env err (lhs, cploc) (rhs, cnloc)

let make_err_nocons env errs (cp,cploc) (cn,cnloc) =
  make_head_err env errs (tcons_head (cp, cploc), cploc) (cn, cnloc)

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

let as_single_var ty vars =
  assert (is_tbot (Tcvj ty));
  match vars with
  | [i, _loc] -> i
  | _ -> assert false

let as_rigvar = function
  | Vbound _ -> intfail "Vbound"
  | Vrigid rv -> rv

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
       conses |> List.map (fun (cons, _loc) ->
         (* FIXME: is matchability assumed for the ptyp_to_lower bits? *)
         Ucons (Cons1.map cons
                  ~neg:(ptyp_to_lower ~simple env)
                  ~pos:(ntyp_to_fresh_flexvar ~simple env)))
     in
     let vars = List.map (fun v -> Urigvar (as_rigvar v, [])) vars in
     let loc = Option.value loc ~default:Location.(fixme "neg loc") in
     Ugen {cons = (conses @ vars, loc); higher_fvs = []}
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
  let sub ~f (a,a_def) (b,b_def) =
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
    match Map.merge sub_field a.fields b.fields with
    | _ -> Ok ()
    | exception (FieldError e) -> Error e

end

module Cons1 = struct
  open Fields
  include Typedefs.Cons1

  let record_def ~env ~shape ~loc {tag; args; body=_} =
    match tag with
    | Some (Named_tag (sym, _)) ->
       let decl_fields = Env.get_decl_fields env sym in
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

  (* least c' greater than c along coe *)
  let coerce_up ~shape env coe c =
    match coe, c with
    | Id, c -> c
    | To_top, _ -> Top
    | Drop_record_tag t, Record r ->
       let body =
         match t with
         | Anon_tag | Struct_tag _ -> r.body
         | Named_tag (s,loc) ->
            Fields.merge ~f:(fun ty _decl -> ty)
              (r.body, record_def ~env ~shape ~loc r)
              (Typedefs.Env.get_decl_fields env s, fun _ -> Fabsent loc)
       in
       Record {tag=None; args=[]; body}
    | Drop_record_tag _, _ -> assert false

  let join ~env ~shape_a ~shape_b ~neg ~pos (a, a_loc) (b, b_loc) =
    assert (sub_head a b = Le Id);
    match a, b with
    | Top, Top -> Top, a_loc
    | (Top, _) | (_, Top) -> assert false

    | Record a, Record b ->
       assert (Option.equal tuple_tag_equal a.tag b.tag);
       let a_def = record_def ~env ~shape:shape_a ~loc:a_loc a in
       let b_def = record_def ~env ~shape:shape_b ~loc:b_loc b in
       Record {tag = a.tag;
               args = List.map2 (Tyarg.zip ~neg ~pos) a.args b.args;
               body = Fields.join ~pos (a.body, a_def) (b.body, b_def) },
       a_loc (* FIXME: which loc is best here? *)

    | Func (args, res), Func (args', res') ->
       let args = List.map2 neg args args' in
       Func(args, pos res res'), a_loc

    | Record _, Func _ | Func _, Record _ -> assert false

  let meet env ~shape_b ~neg ~pos (cons_a, a_loc) (cons_b, b_loc) =
    let open One_or_two in
    (* tree heads means meet exists only for comparable heads *)
    assert (not (incomparable_head cons_a cons_b));

    match cons_a, cons_b with
    | cons_a, Top ->
       cons_a
    | Top, cons_b ->
       Cons1.map cons_b ~neg:(fun x -> neg (R x)) ~pos:(fun x -> pos (R x))
    | Func (args, res), Func (args', res') ->
       let args = List.map2 (fun x y -> neg (LR (x,y))) args args' in
       let res = pos (LR (res, res')) in
       Func (args, res)

    | Record a, Record b ->
       let tag, args =

         match a.tag, b.tag with
         | None, Some (Named_tag _ as tag) ->
            let neg a = neg (R a) and pos a = pos (R a) in
            Some tag, List.map (Tyarg.map ~neg ~pos) b.args

         | None, Some (Anon_tag | Struct_tag _ as tag) ->
            assert (b.args = []);
            Some tag, []

         | Some ta, Some tb ->
            assert (tuple_tag_equal ta tb);
            let neg a b = neg (LR (a, b)) and pos a b = pos (LR (a, b)) in
            Some ta, List.map2 (Tyarg.zip ~neg ~pos) a.args b.args

         | tag, None ->
            assert (b.args = []);
            tag, a.args
       in
       let a_def = record_def ~env ~shape:Type_shape.simple_neg ~loc:a_loc a in
       let b_def = record_def ~env ~shape:shape_b ~loc:b_loc b in
       let body = Fields.meet ~pos (a.body, a_def) (b.body, b_def) in
       Record {tag; args; body}

    | Record _, Func _ | Func _, Record _ -> assert false


  let sub ~env ~shape_a ~shape_b ~neg ~pos (a, a_loc) (b, b_loc) =
    assert (sub_head a b = Le Id);
    match a, b with
    | Top, Top -> Ok ()
    | Func (args, res), Func (args', res') ->
       List.combine args' args
       |> List.iteri (fun i (a', a) -> neg (Func_arg i) a' a);
       pos Func_res res res';
       Ok ()
    | Record a, Record b ->
       assert (Option.equal tuple_tag_equal a.tag b.tag);
       let sub_arg i (arg_a, arg_b) =
         let sym = match a.tag with Some (Named_tag (t,_)) -> t | _ -> assert false in
         ignore (Tyarg.zip arg_a arg_b
                   ~neg:(fun a b -> neg (Named_arg (`Neg, sym, i)) b a)
                   ~pos:(fun a b -> pos (Named_arg (`Pos, sym, i)) a b))
       in
       (match a.tag with Some (Named_tag _) -> () | _ -> assert (a.args = []));
       (match b.tag with Some (Named_tag _) -> () | _ -> assert (b.args = []));
       List.iteri sub_arg (List.combine a.args b.args);
       let sub_field k a b = pos (Record_field k) a b in
       let a_def = record_def ~env ~shape:shape_a ~loc:a_loc a in
       let b_def = record_def ~env ~shape:shape_b ~loc:b_loc b in
       Fields.sub ~f:sub_field (a.body,a_def) (b.body,b_def)
    | _ -> assert false

end

let subtype_cons env ~shape_a ~shape_b ~neg ~pos (cp,cploc) (cn,cnloc) =
  let wrap_err k err = wrap_cons_err (cp, cploc) (cn, cnloc) k err in
  let cp' =
    match Cons1.sub_head cp cn with
    | Un err -> raise (SubtypeError (make_err env (Head err) (cp,cploc) (cn,cnloc)))
    | Le coe -> Cons1.coerce_up ~shape:shape_a env coe cp
  in
  match
    Cons1.sub ~env ~shape_a ~shape_b (cp',cploc) (cn,cnloc)
      ~neg:(fun k a b ->
        try neg a b
        with SubtypeError err -> raise (SubtypeError (wrap_err k err)))
      ~pos:(fun k a b ->
        try pos a b
        with SubtypeError err -> raise (SubtypeError (wrap_err k err)))
  with
  | Ok () -> ()
  | Error err ->
     let err =
       match err with
       | Field_missing (name, ploc, nloc) ->
          make_err env (Field_missing name) (cp, ploc) (cn, nloc)
       | Field_extra (name, ploc, nloc) ->
          make_err env (Field_extra name) (cp, ploc) (cn, nloc)
     in
     raise (SubtypeError err)

let lower_contains_fv fv lower =
  List.exists (function
    | Lflexvar a -> equal_flexvar a fv
    | Lcons (Top, _) -> true
    | _ -> false) lower

let lower_of_rigid_bound env rv : lower =
  Env.rigid_bound env rv
  |> List.map (fun (c,cloc) -> Lcons (c, if cloc == Location.noloc then rv.loc else cloc))

(* Check whether a flex-flex constraint α ≤ β is already present via an upper bound of α *)
let rec has_flex_upper (pv : flexvar) nv =
  pv == nv ||
  match pv.upper with
  | Uflexvar pv' -> has_flex_upper pv' nv
  | Ugen {cons=_; higher_fvs} -> List.memq nv higher_fvs
  | Utop -> false

let upper_cons_map ~neg ~pos ((u,ul) : _ upper_cons Location.loc) : _ upper_cons Location.loc =
  u |> List.map (function
    | Urigvar _ as p -> p
    | Ucons c -> Ucons (Cons1.map ~neg ~pos c)),
  ul

let find_cons_above cp (cns : _ Cons1.t loc list) =
  match
    cns |> List.partition_map (fun (cn,cnloc) ->
      match Cons1.sub_head cp cn with
      | Le hc -> Left (hc, (cn, cnloc))
      | Un r -> Right r)
  with
  | (_ :: _ :: _), _ ->
     intfail "multiple compat cons in upper_cons"
  | [hc, cn], _ ->
     Ok (hc, cn)
  | _, errs ->
     Error (Cons1.merge_head_conflicts errs)

let upper_find_cons cp ((cn : _ upper_cons),cnloc) =
  let cns = cn |> List.filter_map (function Urigvar _ -> None | Ucons cn -> Some (cn,cnloc)) in
  find_cons_above cp cns

let upper_find_rv rv (cn : _ upper_cons) =
  match
    cn
    |> List.filter_map (function
      | Urigvar (rv', ds) when equal_rigvar rv rv' -> Some ds
      | _ -> None)
  with
  | _ :: _ :: _ -> intfail "duplicate RV in upper_cons"
  | [ds] -> Ok ds
  | [] -> Error ()

let upper_cons_is_top (cn : _ upper_cons) =
  match cn with
  | [Ucons Top] -> true
  | _ -> false

let rec match_shape ~changes ~env : (lower, lower -> unit, lower, flexvar) Type_shape.t =
  { of_typ_pos = (fun ~env t -> fun l -> subtype_lu ~changes env l (ntyp_to_upper ~simple:false env t));
    of_typ_neg = (fun ~env t -> ptyp_to_lower ~simple:false env t);
    to_typ_pos = (fun l -> let v = fresh_flexvar (Env.level env) in l [Lflexvar v]; Tsimple v);
    to_typ_neg = (fun t -> Tsimple t) }

and match_sub ~changes env (p : lower_part) ((cn : (lower, lower -> unit) upper_cons), cnloc) : unit =
  let match_shape = match_shape ~changes ~env in
  if upper_cons_is_top cn then ()
  else match p with
  | Lrigvar rv ->
     begin match upper_find_rv rv cn with
     | Ok ds ->
        resolve_delayed_constraints ~changes env ds
     | Error () ->
        Env.rigid_bound env rv |> List.iter (fun (l,lloc) ->
          match upper_find_cons l (cn,cnloc) with
          | Ok (_hc, cn) ->
             subtype_cons env (l, lloc) cn
               ~shape_a:Type_shape.simple_pos
               ~shape_b:match_shape
               ~neg:(fun p n -> subtype_lu ~changes env p (Uflexvar n))
               ~pos:(fun p pr -> pr p)
          | Error err ->
             raise (SubtypeError (make_head_err env err (tvar (Vrigid rv), rv.loc) (cn, cnloc))))
     end
  | Lcons (cp, cploc) ->
     begin match upper_find_cons cp (cn,cnloc) with
     | Ok (_hc, cn) ->
        (* FIXME: use hc instead of recomputing? *)
        subtype_cons env (cp,cploc) cn
          ~shape_a:Type_shape.simple_pos
          ~shape_b:match_shape
          ~neg:(fun p n -> subtype_lu ~changes env p (Uflexvar n))
          ~pos:(fun p pr -> pr p)
     | Error errs ->
        raise (SubtypeError (make_err_nocons env errs (cp, cploc) (cn, cnloc)))
     end

  | Lflexvar pv ->
     let (upper, upper_loc), higher_fvs = rotate_flex ~changes env pv in
     (* shallow scope check *)
     let upper_in_scope = function
       | Urigvar (rv, _) -> Env_level.extends rv.level pv.level
       | Ucons _ -> true
     in
     let cn = List.filter upper_in_scope cn in
     let open struct
       type meet_pair =
         Meet_cons of
           { cons_a: (lower, flexvar) Cons1.t;
             cons_b: (lower, lower -> unit) Cons1.t;
             coe: (Cons1.head_coercion, Cons1.head_coercion) Either.t }
       | Meet_rv of
           { rigvar: rigvar;
             delay: delayed_constraint list }
     end in
     let gen_delayed_constraints rv cons =
       match cons with
       | [Ucons Top], _loc -> Ok []
       | cons ->
          match
            Env.rigid_bound env rv
            |> List.map (fun (cp, cploc) ->
              match upper_find_cons cp cons with
              | Ok (_hc, cn) ->
                 { dy_lower = (cp, cploc);
                   dy_upper = cn;
                   dy_flexvar = pv;
                   dy_resolved = false }
              | Error _ -> raise_notrace Exit)
          with
          | xs -> Ok xs
          | exception Exit -> Error ()
     in
     let meets_a =
       upper |> List.concat_map (function
         | Urigvar (rv, delay_a) ->
            begin match upper_find_rv rv cn with
            | Ok delay_b ->
               let delay =
                 delay_a
                 @ List.filter (fun d -> not (List.memq d delay_a)) delay_b
               in
               [Meet_rv { rigvar = rv; delay }]
            | Error () ->
               (* rv included in output iff up(rv) <= cn *)
               let freshen r =
                 let v = fresh_flexvar pv.level in
                 r [Lflexvar v];
                 v
               in
               let cn' = upper_cons_map ~neg:id ~pos:freshen (cn,cnloc) in
               match gen_delayed_constraints rv cn' with
               | Ok ds -> [Meet_rv {rigvar = rv; delay = delay_a @ ds}]
               | Error () -> []
            end
         | Ucons cons_a ->
            begin match upper_find_cons cons_a (cn,cnloc) with
            | Ok (coe, (cons_b,_loc)) ->
               [Meet_cons {cons_a; cons_b; coe=Left coe}]
            | Error _ -> []
            end)
     in
     let found_new_rv = ref false in
     let cons_decreased = ref false in
     let meets_b =
       cn |> List.concat_map (function
         | Urigvar (rv, delay_b) ->
            begin match upper_find_rv rv upper with
            | Ok _delay_a -> [] (* already in meets_a *)
            | Error () ->
               assert (Env_level.extends rv.level pv.level);
               match gen_delayed_constraints rv (upper,upper_loc) with
               | Ok ds ->
                  found_new_rv := true;
                  [Meet_rv {rigvar = rv; delay = delay_b @ ds}]
               | Error () -> []
            end
         | Ucons cons_b ->
            begin match upper_find_cons cons_b (upper,upper_loc) with
            | Ok (Id, _) -> [] (* already in meets_a *)
            | Ok (coe, (cons_a,_loc)) ->
               cons_decreased := true;
               [Meet_cons {cons_a; cons_b; coe=Right coe}]
            | Error _ -> []
            end)
     in
     let upper =
       (meets_a @ meets_b)
       |> List.map (function
         | Meet_cons {cons_a; cons_b; coe} ->
            let cons_a_changed =
              match coe with
              | Left _ | Right Id -> false
              | Right _ -> true
            in
            let cons_a =
              (* To preserve matchability, need fresh vars if rv set or cons_a changed *)
              if !found_new_rv || cons_a_changed then
                Cons1.map cons_a
                  ~neg:(fun v -> join_lower ~changes env pv.level bottom v)
                  ~pos:(fun v -> let v' = fresh_flexvar pv.level in
                                 subtype_flex_flex ~changes env v' v; v')
              else cons_a
            in
            let cons =
              Cons1.meet env ~shape_b:match_shape
                (cons_a, upper_loc)
                (cons_b, cnloc)
                ~neg:(function
                  | L x -> x
                  | R r -> join_lower ~changes env pv.level bottom r
                  | LR (x, r) -> join_lower ~changes env pv.level x r)
                ~pos:(function
                  | L x -> x
                  | R r -> let v = fresh_flexvar pv.level in r [Lflexvar v]; v
                  | LR (v, r) -> r [Lflexvar v]; v)
            in
            Ucons cons
         | Meet_rv {rigvar; delay} ->
            Urigvar (rigvar, delay))
     in
     (* Format.printf "MSUB %a@." dump_ptyp (Tsimple (of_flexvar pv)); *)
     (* FIXME: better fixpoint check here *)
     wf_ntyp env (Tsimple pv);
     let new_cons_loc =
       if !cons_decreased || upper_loc == Location.noloc then cnloc else upper_loc
     in
     let newbound = Ugen {cons = (upper, new_cons_loc); higher_fvs} in
     if fv_maybe_set_upper ~changes pv newbound then
       subtype_lu ~changes env pv.lower newbound;
     wf_ntyp env (Tsimple pv);
     ()

and resolve_delayed_constraints ~changes env ds =
  ds |> List.iter (fun dy ->
    (* FIXME: when are these resolved for flexvars going out of scope? *)
    assert (Env_level.extends dy.dy_flexvar.level (Env.level env));
    (* FIXME: is recursion ever relevant here? *)
    if not dy.dy_resolved then begin
      dy.dy_resolved <- true;
      try
        subtype_cons env dy.dy_lower dy.dy_upper
          ~shape_a:Type_shape.simple_pos
          ~shape_b:Type_shape.simple_neg
          ~neg:(fun a b -> subtype_lu ~changes env a (Uflexvar b))
          ~pos:(fun a b -> subtype_lu ~changes env a (Uflexvar b))
      with e ->
        dy.dy_resolved <- false;
        (*Format.printf "DELAYFAIL %a <= %a\n%!" pp_ptyp (Tsimple dy.dy_lower) pp_upper dy.dy_upper;*)
        raise e
    end)

and subtype_lpu ~changes env (p : lower_part) (n : upper) =
  match n with
  | Utop -> ()
  | Ugen {cons=cn; higher_fvs} ->
     higher_fvs |> List.iter (fun nv -> subtype_lpu ~changes env p (Uflexvar nv));
     let templ = upper_cons_map cn ~neg:id ~pos:(fun n ->
       fun p -> subtype_lu ~changes env p (Uflexvar n))
     in
     match_sub ~changes env p templ;
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

and rotate_flex ~changes env (pv : flexvar) =
  match pv.upper with
  | Ugen {cons;higher_fvs} -> cons, higher_fvs
  | Utop ->
     let cons, higher_fvs = ([Ucons Top], Location.noloc), [] in
     fv_set_upper ~changes pv (Ugen {cons; higher_fvs});
     assert (equal_upper pv.upper (Ugen {cons; higher_fvs}));
     cons, higher_fvs
  | Uflexvar v' when Env_level.equal v'.level pv.level ->
     let cons, higher_fvs = ([Ucons Top], Location.noloc), [] in
     fv_set_upper ~changes pv (Ugen {cons; higher_fvs});
     noerror (fun () -> subtype_flex_flex ~changes env pv v'); (*FIXME: impl directly?*)
     (* upper may have changed, retry *)
     rotate_flex ~changes env pv
  | Uflexvar v' ->
     let cons, higher_fvs = ([Ucons Top], Location.noloc), [v'] in
     fv_set_upper ~changes pv (Ugen {cons; higher_fvs});
     assert (equal_upper pv.upper (Ugen {cons; higher_fvs}));
     cons, higher_fvs

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
    let pv_cons, pv_higher_fvs = rotate_flex ~changes env pv in
    if Env_level.extends pv.level nv.level then begin
      fv_set_lower ~changes nv (join_lower_part ~changes env nv.level nv.lower (Lflexvar pv));
      subtype_lpu ~changes env (Lflexvar pv) nv.upper
    end else begin
      fv_set_upper ~changes pv (Ugen {cons=pv_cons; higher_fvs = nv::pv_higher_fvs});
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
  let join1 (ca, caloc) (cb, cbloc) = (* ca assumed matchable & correct level *)
    let neg vl vr =
      noerror (fun () -> subtype_flex_flex ~changes env vl vr);
      vl
    in
    let pos a b = join_lower ~changes env level a b in
    Cons1.join ~env ~shape_a:Type_shape.simple_pos ~shape_b:Type_shape.simple_pos ~neg ~pos (ca, caloc) (cb, cbloc)
  in
  let rec join_cons lower ca_acc cb cb_loc =
    match lower with
    | (Lflexvar _ | Lrigvar _) as part :: rest -> part :: join_cons rest ca_acc cb cb_loc
    | Lcons (ca, ca_loc) as part :: rest ->
       begin match Cons1.sub_head cb ca with
       | Le hc -> (* cb <= ca, only once because antichain *)
          Lcons (join1 (ca, ca_loc) (Cons1.coerce_up ~shape:Type_shape.simple_pos env hc cb, cb_loc)) :: rest
       | Un _ ->
          match Cons1.sub_head ca cb with
          | Le hc -> (* ca <= cb *)
             join_cons rest ((Cons1.coerce_up ~shape:Type_shape.simple_pos env hc ca, ca_loc) :: ca_acc) cb cb_loc
          | Un _ ->
             part :: join_cons rest ca_acc cb cb_loc
       end
    | [] ->
       (* Must make cb matchable & at correct level *)
       let cons =
         Cons1.map cb
           ~neg:(fun v -> let v' = fresh_flexvar level in noerror (fun () -> subtype_flex_flex ~changes env v' v); v')
           ~pos:(fun l -> join_lower ~changes env level bottom l),
         cb_loc
       in
       let cons = List.fold_left (fun acc ca -> join1 ca acc) cons ca_acc in
       [Lcons cons]
  in
  match ty with
  | Lflexvar fv -> join_fv lower fv
  | Lrigvar rv ->
     if Env_level.extends rv.level level
     then join_rv lower rv
     else join_lower ~changes env level lower (lower_of_rigid_bound env rv)
  | Lcons (cb, cbloc) -> join_cons lower [] cb cbloc

and join_lower ~changes env level lower (ty : lower) =
  List.fold_left (join_lower_part ~changes env level) lower ty

let join_simple env a b =
  (* FIXME: start with a not bottom. (Improve matchability) *)
  let changes = ref [] in
  let r = bottom in
  let r = join_lower ~changes env (Env.level env) r a in
  let r = join_lower ~changes env (Env.level env) r b in
  r

let check_simple t =
  let rec aux = function
    | Tsimple _ -> ()
    | Tpoly _ -> raise Exit
    | Tcvj (_, _ :: _, _cloc) -> () (* by invariant *)
    | Tcvj (c, [], _cloc) ->
       c |> List.iter (fun (c,_) -> Cons1.map ~neg:aux ~pos:aux c |> ignore)
  in
  match aux t with
  | () -> true
  | exception Exit -> false

let upper_is_bot = function
  | Ugen {cons=([],_); higher_fvs=_} -> true
  | _ -> false


(*
 * Subtyping on typs (polymorphism)
 *)

let enter_rigid env vars rig_names =
  let level = Env_level.extend (Env.level env) in
  let temp_env =
    Env.extend_types env
      ~level
      ~rig_names
      ~rig_defns:(IArray.map (fun (name, _) ->
                    {name; upper=[Top,Location.noloc]}) vars)
  in
  let getrv (conses, vars, loc) vars' =
    let vars = vars @ (List.map (fun (var,loc) -> Vrigid {level;loc;var}) vars') in
    Tcvj (conses, vars, loc)
  in
  let openrig t = open_typ ~neg:getrv ~pos:getrv 0 t in
  let rig_defns = IArray.map (fun (name, b) ->
     let upper =
       match b with
       | None -> [Lcons (Top, Location.noloc)]
       | Some b -> ptyp_to_lower ~simple:true temp_env (openrig b) in
     match upper with
     | [Lcons (Top, loc)] ->
        { name; upper = [Top, loc] }
     | lower ->
       (* FIXME: can you actually hit this?
          Try with a higher-rank type where the outer rank gets instantiated.
          Maybe change the type of the upper bound in parsed types.
          (to reflect its Tconsness)*)
        let conses = lower |> List.map (function
          | Lcons (c,cloc) -> c,cloc
          | Lrigvar _ | Lflexvar _ -> assert false)
        in
        { name; upper = conses }) vars in
  let env = Env.extend_types env ~level ~rig_names ~rig_defns in
  env, openrig

let rec subtype_exn env (p : ptyp) (n : ntyp) =
  (* Format.printf "%a <= %a\n" dump_ptyp p pp_ntyp n; *)
  wf_ptyp env p; wf_ntyp env n;
  match p, n with
  | _, t when is_ttop t -> ()
  | t, _ when is_tbot t -> ()
  | Tcvj (cp,vp,ploc), Tcvj (cns,vn,nloc) ->
     cp |> List.iter (fun (cp,cploc) ->
       match find_cons_above cp cns with
       | Ok (_,cn) ->
          subtype_cons env
            ~shape_a:Type_shape.gen_pos
            ~shape_b:Type_shape.gen_neg
            ~neg:(subtype_exn env) ~pos:(subtype_exn env) (cp,cploc) cn
       | Error err ->
          let tunit _ = Tsimple () in
          let cp = Cons1.map ~neg:tunit ~pos:tunit cp in
          let cns = List.map (fun (c,l) -> Cons1.map ~neg:tunit ~pos:tunit c, l) cns in
          raise (SubtypeError (make_err' env (Head err)
                                 (Tcvj ([cp,cploc],[],ploc), cploc)
                                 (Tcvj (cns,vn,nloc),Option.value nloc ~default:Location.noloc))));
     vp |> List.iter (fun vp ->
       if not (List.exists (equal_typ_var vp) vn) then
         subtype_lu ~changes:(ref []) env [Lrigvar (as_rigvar vp)] (ntyp_to_upper ~simple:false env n));
  | p, Tpoly {vars; body} ->
     let orig_env = env in
     let env, open_rvars = enter_rigid env vars SymMap.empty in
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

(* FIXME: rank1 joins maybe?
   FIXME: keep types as Tcons if possible? Better inference. Can this matter? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  if is_tbot p then q
  else if is_tbot q then p
  else
    let p = ptyp_to_lower ~simple:false env p in
    let q = ptyp_to_lower ~simple:false env q in
    Tsimple (join_simple env p q)

(* FIXME: is this ever needed in nontrivial ways? *)
let meet_ntyp env (p : ntyp) (q : ntyp) : ntyp =
  if is_ttop p then q
  else if is_ttop q then p
  else
     let v = fresh_flexvar (Env.level env) in
     subtype_lpu ~changes:(ref []) env (Lflexvar v) (ntyp_to_upper ~simple:false env p);
     subtype_lpu ~changes:(ref []) env (Lflexvar v) (ntyp_to_upper ~simple:false env q);
     Tsimple v

let rec match_ptyp ~loc env (p : ptyp) (heads : (ntyp->unit, ptyp->unit) upper_cons) =
  let match_shape : (ntyp->unit, ptyp->unit, lower, flexvar) Type_shape.t =
    { of_typ_pos = (fun ~env (n:ntyp) -> fun p -> subtype_exn env p n);
      of_typ_neg = (fun ~env (p:ptyp) -> fun n -> subtype_exn env p n);
      to_typ_pos = (fun t -> let v = fresh_flexvar (Env.level env) in t (Tsimple [Lflexvar v]); Tsimple v);
      to_typ_neg = (fun t -> let v = fresh_flexvar (Env.level env) in t (Tsimple v); Tsimple [Lflexvar v])}
  in
  match p with
  (* FIXME: Can/should this work with vars too? *)
  | Tcvj (conses, [], _jloc) ->
     conses |> List.iter (fun (c, cloc) ->
       match upper_find_cons c (heads,loc) with
       | Ok (_hc, head) ->
          subtype_cons env (c, cloc) head
            ~shape_a:Type_shape.gen_pos
            ~shape_b:match_shape
            ~neg:(fun v t -> v t)
            ~pos:(fun t v -> v t)
       | Error err ->
          raise (SubtypeError (make_err_nocons env err (c, cloc) (heads, loc))))
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_ptyp ~loc env body heads
  | t ->
     let instneg v =
       let fv = fresh_flexvar (Env.level env) in
       v (Tsimple fv);
       [Lflexvar fv] in
     let shead = upper_cons_map ~neg:instneg ~pos:(fun v -> fun p -> v (Tsimple p)) (heads,loc) in
     ptyp_to_lower ~simple:false env t
     |> List.iter (fun l -> match_sub ~changes:(ref []) env l shead)

let match_ptyp ~loc env ty heads =
  let heads = List.map (fun cons ->
    let cons = Cons1.map cons
      ~neg:(fun r -> fun t -> r := meet_ntyp env !r t)
      ~pos:(fun r -> fun t -> r := join_ptyp env !r t)
    in Ucons cons) heads
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
  | Ugen {cons=(cn,cnloc); higher_fvs} ->
    List.exists (fun a' -> clearly_subtype env a' b) higher_fvs ||
    cn |> List.for_all (fun u ->
      b |> List.exists (fun l ->
        match u, l with
        | Urigvar (rv, _ds), Lrigvar rv' ->
           (* It is correct to ignore ds here, since LHS is either rv or Bot *)
           equal_rigvar rv rv'
        | Ucons cn, Lcons (cp, cploc) when Cons1.sub_head cn cp = Le Id ->
           let sub _k a b = if not (clearly_subtype env a b) then raise Exit in
           begin match Cons1.sub ~env ~shape_a:Type_shape.simple_neg ~shape_b:Type_shape.simple_pos ~neg:sub ~pos:sub (cn,cnloc) (cp,cploc) with
           | Ok () -> true
           | Error _ -> false
           | exception Exit -> false
           end
        | _ -> false))

let rec clearly_subtype_typ env (a : ntyp) (b : ptyp) : bool =
  match a, b with
  | Tcvj (cons_a, vars_a, _), Tcvj (cons_b, vars_b, _) ->
     vars_a |> List.for_all (fun a -> vars_b |> List.exists (equal_typ_var a))
     &&
     cons_a |> List.for_all (fun (a,aloc) ->
       cons_b |> List.exists (fun (b,bloc) ->
         let sub _ a b = if not (clearly_subtype_typ env a b) then raise Exit in
         Cons1.sub_head a b = Le Id &&
         match Cons1.sub ~env ~shape_a:Type_shape.gen_neg ~shape_b:Type_shape.gen_pos ~neg:sub ~pos:sub (a,aloc) (b,bloc) with
         | Ok () -> true
         | Error _ -> false
         | exception Exit -> false))
  | a, b ->
     clearly_subtype env
       (ntyp_to_fresh_flexvar ~simple:false env a)
       (ptyp_to_lower ~simple:false env b)

let rec map_typ_0 : 'neg1 'pos1 'neg2 'pos2 .
  neg:(index:int -> 'neg1 -> ('pos2, 'neg2) typ) ->
  pos:(index:int -> 'pos1 -> ('neg2, 'pos2) typ) ->
  index:int -> ('neg1, 'pos1) typ -> ('neg2, 'pos2) typ =
  fun ~neg ~pos ~index -> function
  | Tcvj (conses, vars, loc) ->
     let conses =
       conses |> List.map (fun (c, cloc) ->
         Cons1.map c
           ~neg:(map_typ_0 ~pos:neg ~neg:pos ~index)
           ~pos:(map_typ_0 ~neg ~pos ~index),
         cloc)
     in
     Tcvj (conses, vars, loc)
  | Tsimple t -> pos ~index t
  | Tpoly {vars; body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (n, t) -> n, Option.map (map_typ_0 ~neg:pos ~pos:neg ~index) t) vars in
     let body = map_typ_0 ~neg ~pos ~index body in
     Tpoly {vars; body}

let map_typ_1 ~neg ~pos ~index t =
  let neg ~index:_ t = Tsimple (neg t) in
  let pos ~index:_ t = Tsimple (pos t) in
  map_typ_0 ~neg ~pos ~index t

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
               let _, _ = rotate_flex ~changes env pv in
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
          let cons, higher_fvs = rotate_flex ~changes env nv in
             let change = ref false in
             let cons =
               upper_cons_map cons
                 ~neg:(fun x ->
                   let x' = expand_lower visit ~changes env x in
                   if not (equal_lower x x') then change := true;
                   x')
                 ~pos:(expand_fv_neg visit ~changes env)
             in
             (* FIXME change tracking *)
             if true || !change then ignore (fv_maybe_set_upper ~changes nv (Ugen {cons=cons; higher_fvs}))
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

let trim_overrides s = function
  | Cons1.Record r, loc ->
     let def = Cons1.record_def ~env:s.env ~shape:Type_shape.gen ~loc r in
     let no _ _ = false in
     let eq = Fields.equal_field_desc (Typedefs.equal_typ ~neg:no ~pos:no) in
     let body = Fields.filteri r.body ~f:(fun fn x -> not (eq x (def fn))) in
     Cons1.Record {r with body}, loc
  | cons -> cons

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
  let conses = List.map (trim_overrides s) conses in
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
     let c, loc, vars =
       match u with
       | Utop -> [Ucons Top], Location.noloc, []
       | Uflexvar v -> [Ucons Top], Location.noloc, [v]
       | Ugen {cons=(c,loc); higher_fvs} -> c, loc, higher_fvs
     in
     let conses, rigvars = c |> List.partition_map (function
        | Urigvar (r,ds) ->
           begin match List.find_opt (fun d -> not d.dy_resolved) ds with
           | None ->
              Either.Right (Some (promote_rigvar s r));
           | Some _dy ->
              (* FIXME: It would be sound to drop these variables. Would that be weird? *)
              unimp "unresolved delayed constraints"
(*                pp_ptyp (Tsimple [Lcons dy.dy_lower]) pp_upper (Ugen {cons=([Ucons (fst dy.dy_upper)], snd dy.dy_upper);higher_fvs=[]})*)
              (* Either.Right None *)
           end
        | Ucons c ->
           let c = Cons1.map ~neg:(promote_lower s) ~pos:(promote_fv_neg s) c in
           Either.Left (trim_overrides s (c,loc))) in
     vars, Tcvj (conses, List.filter_map id rigvars, Some loc)


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
       | Utop | Ugen {cons=_; higher_fvs=[]} -> false
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
    P.map ty
      ~neg:(fun ~mode ~ext t ->
        let index = List.length ext in
        map_typ_0 ~neg:(pos_simple ~mode) ~pos:(neg_simple ~mode) ~index t)
      ~pos:(fun ~mode ~ext t ->
        let index = List.length ext in
        map_typ_0 ~neg:(neg_simple ~mode) ~pos:(pos_simple ~mode) ~index t)
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
  bvars, ty

end
