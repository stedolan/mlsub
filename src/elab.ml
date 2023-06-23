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

(* pottier-style applicative functor for elaboration *)
type _ elab_req =
  | Unit : unit elab_req
  | Pair : 's elab_req * 't elab_req -> ('s * 't) elab_req
  | Ptyp : ptyp -> tyexp elab_req
  | Ntyp : ntyp -> tyexp elab_req
  | Gen :
      { bounds : (string Location.loc * ntyp option) IArray.t;
        body : 'a elab_req } ->
      (typolybounds * 'a) elab_req
type +'a elab =
  | Elab : 'r elab_req * ('r -> 'a) -> 'a elab

let elab_pure x = Elab (Unit, fun () -> x)
let elab_map g (Elab (r, f)) = Elab (r, fun x -> g (f x))
let elab_pair (Elab (a, f)) (Elab (b, g)) = Elab (Pair (a, b), fun (a, b) -> f a, g b)
let elab_ptyp ty = Elab (Ptyp ty, fun x -> x)
let elab_ntyp ty = Elab (Ntyp ty, fun x -> x)

let (let* ) x f = elab_map f x
let (and* ) a b = elab_pair a b

let elab_fields (f : 'a elab tuple_fields) : 'a tuple_fields elab =
  let fields =
    List.fold_left (fun acc n ->
      let* acc = acc
      and* x = FieldMap.find n f.fields in
      FieldMap.add n x acc) (elab_pure FieldMap.empty) f.fnames in
  let* fields = fields in
  { f with fields }

let rec elab_list (xs : 'a elab list) : 'a list elab =
  match xs with
  | [] -> elab_pure []
  | x :: xs -> let* x = x and* xs = elab_list xs in x :: xs

let rec elaborate : type a . env:_ -> a elab_req -> a =
  fun ~env rq -> match rq with
  | Unit -> ()
  | Pair (s, t) -> (elaborate ~env s, elaborate ~env t)
  | Ptyp t -> unparse_ptyp ~flexvar:ignore ~env t
  | Ntyp t -> unparse_ntyp ~flexvar:ignore ~env t
  | Gen { bounds; body } ->
     let env, bounds = unparse_bounds ~env ~pos:(unparse_flex_lower_bound ~flexvar:ignore) ~neg:(unparse_flexvar ~flexvar:ignore) bounds in
     bounds, elaborate ~env body

let rec elabreq_map_typs :
  type a . neg:_ -> pos:_ -> index:int -> a elab_req -> a elab_req =
  fun ~neg ~pos ~index rq -> match rq with
  | Unit -> Unit
  | Pair (s, t) -> Pair (elabreq_map_typs ~neg ~pos ~index s,
                         elabreq_map_typs ~neg ~pos ~index t)
  | Ptyp p -> Ptyp (pos ~index p)
  | Ntyp n -> Ntyp (neg ~index n)
  | Gen {bounds; body} ->
     let index = index + 1 in
     let bounds = IArray.map (fun (n,b) -> n, Option.map (neg ~index) b) bounds in
     let body = elabreq_map_typs ~neg ~pos ~index body in
     Gen{bounds;body}


let elaborate env (Elab (rq, k)) = k (elaborate ~env:(env,[]) rq)


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


(*
let rec wf_elab_req : type a . _ -> a elab_req -> unit =
  fun env rq -> match rq with
  | Unit -> ()
  | Pair (s, t) ->
     wf_elab_req env s;
     wf_elab_req env t
  | Ptyp t ->
     wf_ptyp env t
  | Ntyp t ->
     wf_ntyp env t
  | Gen { pol; bounds; flow; body } ->
     (* toplevel references to bound variables should be in flow, not bounds *)
     bounds |> Array.iter (fun (_name, p, n) ->
       assert (p.bound = []); assert (n.bound = []));
     let env, _, inst = enter_poly' pol env SymMap.empty bounds flow in
     let body = map_bound_elab_req (binder_sort pol) 0 inst body in
     wf_elab_req env body


let elaborate env (Elab (rq, k)) = k (elaborate env rq)

open PPrint
let rec pr_elab_req : type a . a elab_req -> document = function
  | Unit -> empty
  | Pair (s, t) -> pr_elab_req s ^^ pr_elab_req t
  | Typ (pol, t) -> pr_typ pol t ^^ hardline
  | Gen {pol; bounds=_; flow=_; body} ->
     utf8string "∀" ^^ (match pol with Pos -> utf8string "⁺" | Neg -> utf8string "⁻") ^^ nest 2 (hardline ^^ pr_elab_req body)

*)

let rec pp_elab_req : type a . _ -> a elab_req -> _ =
  fun ppf rq -> match rq with
  | Unit -> ()
  | Pair (p, q) -> pp_elab_req ppf p; pp_elab_req ppf q
  | Ptyp p -> Format.fprintf ppf "PTYP: %a\n" dump_ptyp p
  | Ntyp q -> Format.fprintf ppf "NTYP: %a\n" pp_ntyp q
  | Gen g -> Format.fprintf ppf "GEN\n"; pp_elab_req ppf g.body
