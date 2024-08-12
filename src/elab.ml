open Util
open Tuple_fields
open Typedefs
open Exp
open Location

type ('n,'p) elab_typ =
  | Elab_ptyp of ('n, 'p) typ
  | Elab_ntyp of ('p, 'n) typ

type ('n,'p) typed_exp = ('n, 'p) typed_exp' mayloc and ('n, 'p) typed_exp' =
  | Lit of literal loc
  | Var of ident * value_binding (* Is this right? *)
  | Fn of ('n, 'p) typed_func_def
  | FnDef of symbol * IR.value IR.Binder.t * ('n, 'p) typed_func_def * ('n, 'p) typed_exp
  | App of ('n,'p) typed_exp * ('n,'p) typed_exp list (* FIXME: restore/preserve parameter names? *)
  | Tuple of tuple_tag option * (field_name loc * ('n,'p) typed_exp) list
  | Let of typed_pat * Check_pat.ex_split * ('n,'p) elab_typ * ('n,'p) typed_exp * ('n,'p) typed_exp Check_pat.action
  | Seq of ('n,'p) typed_exp * ('n, 'p) typed_exp
  | Proj of ('n, 'p) typed_exp * symbol
  | If of ('n, 'p) typed_exp * ('n, 'p) typed_exp * ('n, 'p) typed_exp
  | Match of ('n, 'p) typed_exp list loc * Check_pat.ex_split * ('n, 'p) typed_case list
  | Typed of ('n, 'p) typed_exp * ('n, 'p) elab_typ
  | Pragma of string

and ('n, 'p) typed_case = typed_pat list list loc * ('n, 'p) typed_exp Check_pat.action

and ('n, 'p) typed_func_def =
  ('n, 'p) typed_polybounds option * ('n, 'p) typed_parameters * Check_pat.ex_split * ('n, 'p) typ option * ('n, 'p) typed_exp Check_pat.action

and ('n, 'p) typed_parameters =
  (typed_pat * ('p, 'n) typ option) list

and typed_pat = pat

and ('n, 'p) typed_polybounds =
  (string Location.loc * ('p,'n) typ option) IArray.t

let map_elab_typ ~neg ~pos ~index = function
  | Elab_ptyp t -> Elab_ptyp (pos ~index t)
  | Elab_ntyp t -> Elab_ntyp (neg ~index t)

let rec typed_map_typs_exp ~neg ~pos ~index (e : _ typed_exp) =
  match e with
  | None, _ as e -> e
  | Some e, loc -> Some (typed_map_typs_exp' ~neg ~pos ~index e), loc

and typed_map_typs_exp' ~neg ~pos ~index = function
  | Lit _ as e -> e
  | Var _ as e -> e (* FIXME value_binding? *)
  | Fn fndef ->
     Fn (typed_map_func_def ~neg ~pos ~index fndef)
  | FnDef (s, vb, fndef, body) ->
     FnDef (s, vb, typed_map_func_def ~neg ~pos ~index fndef, typed_map_typs_exp ~neg ~pos ~index body)
  | App (f, args) ->
     App (typed_map_typs_exp ~neg ~pos ~index f,
          List.map (fun x -> typed_map_typs_exp ~neg ~pos ~index x) args)
  | Tuple (tag, fs) ->
     Tuple (tag, List.map (fun (fn, x) -> fn, typed_map_typs_exp ~neg ~pos ~index x) fs)
  | Let (p, split, ty, e, body) ->
     (* FIXME binding? *)
     Let (p, split, map_elab_typ ~neg ~pos ~index ty, typed_map_typs_exp ~neg ~pos ~index e, typed_map_typs_action ~neg ~pos ~index body)
  | Seq (e1, e2) ->
     Seq (typed_map_typs_exp ~neg ~pos ~index e1,
          typed_map_typs_exp ~neg ~pos ~index e2)
  | Proj (e, s) ->
     Proj (typed_map_typs_exp ~neg ~pos ~index e, s)
  | If (cond, ifso, ifnot) ->
     If (typed_map_typs_exp ~neg ~pos ~index cond,
         typed_map_typs_exp ~neg ~pos ~index ifso,
         typed_map_typs_exp ~neg ~pos ~index ifnot)
  | Match ((es,matchloc), split, cases) ->
     Match ((List.map (typed_map_typs_exp ~neg ~pos ~index) es, matchloc),
            split,
            List.map (fun (pats, e) -> pats, typed_map_typs_action ~neg ~pos ~index e) cases)
  | Typed (e, ty) ->
     Typed (typed_map_typs_exp ~neg ~pos ~index e, map_elab_typ ~neg ~pos ~index ty)
  | Pragma _ as e -> e


and typed_map_typs_action ~neg ~pos ~index Check_pat.{ rhs; id; pat_loc; bindings } =
  let rhs = typed_map_typs_exp ~neg ~pos ~index rhs in
  let map_binding (vb : value_binding) =
    (* FIXME what's wrong with this? *)
    (*{ vb with typ = pos ~index vb.typ }*) vb in
  let bindings = Option.map (fun (b : Check_pat.act_bindings) -> { b with bindings = SymMap.map map_binding b.Check_pat.bindings }) bindings in
  Check_pat.{ rhs; id; pat_loc; bindings }

and typed_map_func_def ~neg ~pos ~index (poly, params, psplit, ret, body) =
  let poly, index =
    match poly with
    | None -> None, index
    | Some bounds ->
       let index = index + 1 in
       Some (IArray.map (fun (n, b) -> n, Option.map (neg ~index) b) bounds), index
  in
  let params = List.map (fun (p, ty) -> p, Option.map (neg ~index) ty) params in
  let ret = Option.map (pos ~index) ret in
  let body = typed_map_typs_action ~neg ~pos ~index body in
  poly, params, psplit, ret, body

module Elaborate = struct
  let rec exp env (e : _ typed_exp) : exp =
    match e with
    | None, l -> None, l
    | Some e, l -> Some (exp' env e), l

  and exp' env : _ typed_exp' -> exp' = function
    | Lit l -> Lit l
    | Var ((id,loc),_v) -> Var (id, loc)
    | Fn fn -> Fn (fndef env fn)
    | FnDef (s, _vb, fn, body) ->
       FnDef (s, fndef env fn, exp env body)
    | App (f, args) ->
       App (exp env f, List.map (fun e -> None (*FIXME*), exp env e) args)
    | Tuple (tag, fs) ->
       Tuple (tag, tuple env fs)
    | Let (p, _split, ty, e, body) ->
       Let (p, Some (typ env ty), exp env e, exp env body.rhs)
    | Seq (e1, e2) ->
       Seq (exp env e1, exp env e2)
    | Proj (e, s) ->
       Proj (exp env e, s)
    | If (cond, ifso, ifnot) ->
       If (exp env cond, exp env ifso, exp env ifnot)
    | Match ((es,loc), _split, cases) ->
       Match ((List.map (exp env) es,loc), List.map (case env) cases)
    | Typed (e, ty) ->
       Typed (exp env e, typ env ty)
    | Pragma s ->
       Pragma s

  and tuple env fields =
    fields
    |> List.map (function
        | (Field_named k, _) as f,
          (Some (Var (({label=s';shift=0},_), _)), _) when k = s' ->
           f, Mandatory, None
        | f, e ->
           f, Mandatory, Some (exp env e))
    |> Exp.of_record_fields ~fopen:Ext_closed

  and case env (ps, e) = (ps, exp env e.rhs)

  and typ env = function
    | Elab_ptyp t -> unparse_ptyp ~flexvar:ignore ~env t
    | Elab_ntyp t -> unparse_ntyp ~flexvar:ignore ~env t

  and fndef env (poly, params, _psplit, ret, body) =
    let env, poly =
      match poly with
      | None ->
         env, None
      | Some bounds ->
         let env, poly =
           unparse_bounds ~env ~pos:(fun ~env (Vflex fv) -> unparse_flexvar ~env ~flexvar:ignore fv) ~neg:(unparse_flexvar ~flexvar:ignore) bounds
         in
         env, Some poly
    in
    poly,
    List.map (fun (p, t) -> p, Option.map (unparse_ntyp ~flexvar:ignore ~env) t) params,
    Option.map (unparse_ptyp ~flexvar:ignore ~env) ret,
    exp env body.rhs

end


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

let tuple tag (fields : (field_name * exp) list) =
  fun k ->
  eval_cont_list (List.map snd fields) @@ fun vs ->
  apply_cont k (Tuple (tag, List.map2 (fun (f, _) v -> f, v) fields vs))

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
  eval_cont_list args @@ fun args ->
  let vret = IR.Binder.fresh ~name:"x" () in
  Apply (Func fn, args, [vret],
         apply_cont k (IR.var vret))

let trap s : exp =
  fun _k ->
  Trap s

end


module Compile = struct
  module IRB = IR_Builder

  let pat_name = function
    | Some (Pbind (v,_)), _ -> Some (fst v : string)
    | _ -> None

  let rec exp (e : _ typed_exp) : IRB.exp =
    match e with
    | None, _loc -> IRB.trap "type error?"
    | Some e, _loc ->
       exp' e

  and exp' : _ typed_exp' -> IRB.exp = function
    | Lit (l, _) -> IRB.literal l
    | Var (_, v) -> IRB.var v.comp_var
    | Typed (e, _ty) -> exp e
    | If (cond, ifso, ifnot) ->
       fun k ->
       IRB.name_cont k @@ fun k ->
       IRB.eval_cont (exp cond) @@ fun cond ->
       Match (cond, [
         (IR.Symbol.of_string "true", ([], exp ifso (Named_cont k)));
         (IR.Symbol.of_string "false", ([], exp ifnot (Named_cont k)))], None)

    | App (f, args) ->
       IRB.apply (exp f) (List.map exp args)

    | Tuple (tag, fields) ->
       (let tag = Option.map (fun (t,_) -> IR.Symbol.of_string t) tag in
        IRB.tuple tag (List.map (fun ((fn,_loc), e) -> (fn, exp e)) fields))

    | Proj (e, (field, _loc)) ->
       IRB.project (exp e) field

    | Seq (e1, e2) ->
       fun k ->
       IRB.eval_cont (exp e1) @@ fun _v ->
       exp e2 k

    | Match ((es,_loc), split, cases) ->
       fun k ->
         let actions = List.map (fun (_pats, act) ->
                           {act with Check_pat.rhs = exp act.Check_pat.rhs}) cases in
         let actions = Array.of_list actions in
         IRB.maybe_dup_cont ~uses:(Array.length actions) k @@ fun k ->
         IRB.eval_cont_list (List.map (fun e -> exp e) es) @@ fun vals ->
         Check_pat.compile ~cont:k ~actions vals split

    | Let (_p, split, _ty, e, act) ->
       fun k ->
         let actions = [| { act with Check_pat.rhs = exp act.Check_pat.rhs } |] in
         IRB.eval_cont (exp e) @@ fun e ->
         Check_pat.compile ~cont:k ~actions [e] split

    | Fn def ->
       fun k -> IRB.apply_cont k (func_def def)

    | FnDef (_sym, vb, fndef, body) ->
       fun k -> LetVal(vb, func_def fndef, exp body k)

    | Pragma "true" ->
       IRB.literal (Bool true)
    | Pragma "false" ->
       IRB.literal (Bool false)
    | Pragma "bot" ->
       IRB.trap "@bot"
    | Pragma _ ->
       intfail "unknown pragma"

  and func_def ((_poly,params,psplit,_ret,body) : _ typed_func_def) : IR.value =
    let actions = [| { body with rhs = exp body.rhs } |] in
    let params =
      List.map (fun (pat, _) ->
        IR.Binder.fresh ?name:(pat_name pat) ()) params
    in
    let ret = IR.Binder.fresh () in
    Lambda(params,
           ret,
           Check_pat.compile ~cont:(IRB.Named_cont (IR.Binder.ref ret)) ~actions (List.map IR.var params) psplit)
end
