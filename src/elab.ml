open Util
open Tuple_fields
open Typedefs
open Exp
open Location

type elab_typ =
  | Elab_ptyp of ptyp
  | Elab_ntyp of ntyp

type typed_exp = typed_exp' mayloc and typed_exp' =
  | Lit of literal loc
  | Var of ident * value_binding (* Is this right? *)
  | Fn of typed_func_def
  | FnDef of symbol * typed_func_def * typed_exp
  | App of typed_exp * typed_exp tuple_fields
  | Tuple of tuple_tag option * typed_exp tuple_fields
  | Let of typed_pat * elab_typ * typed_exp * typed_exp
  | Seq of typed_exp * typed_exp
  | Proj of typed_exp * symbol
  | If of typed_exp * typed_exp * typed_exp
  | Match of typed_exp list loc * typed_case list
  | Typed of typed_exp * elab_typ
  | Pragma of string

and typed_case = typed_pat list list loc * typed_exp

and typed_func_def =
  typed_polybounds option * typed_parameters * ptyp option * typed_exp

and typed_parameters =
  (typed_pat * ntyp option) tuple_fields

and typed_pat = pat

and typed_polybounds =
  (string Location.loc * ntyp option) IArray.t

let map_elab_typ ~neg ~pos ~index = function
  | Elab_ptyp t -> Elab_ptyp (pos ~index t)
  | Elab_ntyp t -> Elab_ntyp (neg ~index t)

let rec typed_map_typs_exp ~neg ~pos ~index (e : typed_exp) =
  match e with
  | None, _ -> e
  | Some e, loc -> Some (typed_map_typs_exp' ~neg ~pos ~index e), loc

and typed_map_typs_exp' ~neg ~pos ~index = function
  | Lit _ as e -> e
  | Var _ as e -> e (* FIXME value_binding? *)
  | Fn fndef ->
     Fn (typed_map_func_def ~neg ~pos ~index fndef)
  | FnDef (s, fndef, body) ->
     FnDef (s, typed_map_func_def ~neg ~pos ~index fndef, typed_map_typs_exp ~neg ~pos ~index body)
  | App (f, args) ->
     App (typed_map_typs_exp ~neg ~pos ~index f,
          Tuple_fields.map_fields (fun _fn x -> typed_map_typs_exp ~neg ~pos ~index x) args)
  | Tuple (tag, fs) ->
     Tuple (tag, Tuple_fields.map_fields (fun _fn x -> typed_map_typs_exp ~neg ~pos ~index x) fs)
  | Let (p, ty, e, body) ->
     (* FIXME binding? *)
     Let (p, map_elab_typ ~neg ~pos ~index ty, typed_map_typs_exp ~neg ~pos ~index e, typed_map_typs_exp ~neg ~pos ~index body)
  | Seq (e1, e2) ->
     Seq (typed_map_typs_exp ~neg ~pos ~index e1,
          typed_map_typs_exp ~neg ~pos ~index e2)
  | Proj (e, s) ->
     Proj (typed_map_typs_exp ~neg ~pos ~index e, s)
  | If (cond, ifso, ifnot) ->
     If (typed_map_typs_exp ~neg ~pos ~index cond,
         typed_map_typs_exp ~neg ~pos ~index ifso,
         typed_map_typs_exp ~neg ~pos ~index ifnot)
  | Match ((es,matchloc), cases) ->
     Match ((List.map (typed_map_typs_exp ~neg ~pos ~index) es, matchloc),
            List.map (fun (pats, e) -> pats, typed_map_typs_exp ~neg ~pos ~index e) cases)
  | Typed (e, ty) ->
     Typed (typed_map_typs_exp ~neg ~pos ~index e, map_elab_typ ~neg ~pos ~index ty)
  | Pragma _ as e -> e

and typed_map_func_def ~neg ~pos ~index (poly, params, ret, body) =
  let poly, index =
    match poly with
    | None -> None, index
    | Some bounds ->
       let index = index + 1 in
       Some (IArray.map (fun (n, b) -> n, Option.map (neg ~index) b) bounds), index
  in
  let params = Tuple_fields.map_fields (fun _fn (p, ty) -> p, Option.map (neg ~index) ty) params in
  let ret = Option.map (pos ~index) ret in
  let body = typed_map_typs_exp ~neg ~pos ~index body in
  poly, params, ret, body

module Elaborate = struct
  let rec exp env (e : typed_exp) : exp =
    match e with
    | None, l -> None, l
    | Some e, l -> Some (exp' env e), l

  and exp' env : typed_exp' -> exp' = function
    | Lit l -> Lit l
    | Var ((id,loc),_v) -> Var (id, loc)
    | Fn fn -> Fn (fndef env fn)
    | FnDef (s, fn, body) ->
       FnDef (s, fndef env fn, exp env body)
    | App (f, args) ->
       App (exp env f, map_fields (fun _fn e -> exp env e) args)
    | Tuple (tag, fs) ->
       Tuple (tag, map_fields (fun _fn e -> exp env e) fs)
    | Let (p, ty, e, body) ->
       Let (p, Some (typ env ty), exp env e, exp env body)
    | Seq (e1, e2) ->
       Seq (exp env e1, exp env e2)
    | Proj (e, s) ->
       Proj (exp env e, s)
    | If (cond, ifso, ifnot) ->
       If (exp env cond, exp env ifso, exp env ifnot)
    | Match ((es,loc), cases) ->
       Match ((List.map (exp env) es,loc), List.map (case env) cases)
    | Typed (e, ty) ->
       Typed (exp env e, typ env ty)
    | Pragma s ->
       Pragma s

  and case env (ps, e) = (ps, exp env e)

  and typ env = function
    | Elab_ptyp t -> unparse_ptyp ~flexvar:ignore ~env t
    | Elab_ntyp t -> unparse_ntyp ~flexvar:ignore ~env t

  and fndef env (poly, params, ret, body) =
    let env, poly =
      match poly with
      | None ->
         env, None
      | Some bounds ->
         let env, poly =
           unparse_bounds ~env ~pos:(unparse_flex_lower_bound ~flexvar:ignore) ~neg:(unparse_flexvar ~flexvar:ignore) bounds
         in
         env, Some poly
    in
    poly,
    map_fields (fun _fn (p, t) -> p, Option.map (unparse_ntyp ~flexvar:ignore ~env) t) params,
    Option.map (unparse_ptyp ~flexvar:ignore ~env) ret,
    exp env body
         
end
