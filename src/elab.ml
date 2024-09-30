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
  | Var of ident * IR.value IR.Binder.ref
  | Fn of typed_func_def
  | FnDef of symbol * IR.value IR.Binder.t * typed_func_def * typed_exp
  | App of typed_exp * typed_exp list (* FIXME: restore/preserve parameter names? *)
  | Tuple of tuple_tag option * (field_name loc * typed_exp) list
  | Let of typed_pat * Check_pat.ex_split * elab_typ * typed_exp * typed_action
  | Seq of typed_exp * typed_exp
  | Proj of typed_exp * symbol
  | If of typed_exp * typed_exp * typed_exp
  | Match of typed_exp list loc * Check_pat.ex_split * typed_case list
  | Typed of typed_exp * elab_typ
  | Pragma of string

and typed_case = typed_pat list list loc * typed_action

and typed_func_def =
  typed_polybounds option * typed_parameters * Check_pat.ex_split * elab_typ option * typed_action

and typed_parameters =
  (typed_pat * elab_typ option) list

and typed_action =
  { act_body: typed_exp;
    act_bindings: (elab_typ * IR.value IR.Binder.ref) SymMap.t;
    act_comp_bindings: [`Unused | `Once | `Shared of Check_pat.shared_cont] }

and typed_pat = pat

and typed_polybounds =
  (string Location.loc * elab_typ option) IArray.t

type typed_decl =
  | Dfn of symbol * typed_func_def
  | Dtype of Typedefs.type_decl

let map_elab_typ ~neg ~pos ~ext = function
  | Elab_ptyp t -> Elab_ptyp (pos ~ext t)
  | Elab_ntyp t -> Elab_ntyp (neg ~ext t)

let rec typed_map_typs_exp ~neg ~pos ~ext (e : typed_exp) =
  match e with
  | None, _ as e -> e
  | Some e, loc -> Some (typed_map_typs_exp' ~neg ~pos ~ext e), loc

and typed_map_typs_exp' ~neg ~pos ~ext = function
  | Lit _ as e -> e
  | Var (id, v) -> Var (id, v)
  | Fn fndef ->
     Fn (typed_map_func_def ~neg ~pos ~ext fndef)
  | FnDef (s, vb, fndef, body) ->
     FnDef (s, vb, typed_map_func_def ~neg ~pos ~ext fndef, typed_map_typs_exp ~neg ~pos ~ext body)
  | App (f, args) ->
     App (typed_map_typs_exp ~neg ~pos ~ext f,
          List.map (fun x -> typed_map_typs_exp ~neg ~pos ~ext x) args)
  | Tuple (tag, fs) ->
     Tuple (tag, List.map (fun (fn, x) -> fn, typed_map_typs_exp ~neg ~pos ~ext x) fs)
  | Let (p, split, ty, e, body) ->
     (* FIXME binding? *)
     Let (p, split, map_elab_typ ~neg ~pos ~ext ty, typed_map_typs_exp ~neg ~pos ~ext e, typed_map_typs_action ~neg ~pos ~ext body)
  | Seq (e1, e2) ->
     Seq (typed_map_typs_exp ~neg ~pos ~ext e1,
          typed_map_typs_exp ~neg ~pos ~ext e2)
  | Proj (e, s) ->
     Proj (typed_map_typs_exp ~neg ~pos ~ext e, s)
  | If (cond, ifso, ifnot) ->
     If (typed_map_typs_exp ~neg ~pos ~ext cond,
         typed_map_typs_exp ~neg ~pos ~ext ifso,
         typed_map_typs_exp ~neg ~pos ~ext ifnot)
  | Match ((es,matchloc), split, cases) ->
     Match ((List.map (typed_map_typs_exp ~neg ~pos ~ext) es, matchloc),
            split,
            List.map (fun (pats, e) -> pats, typed_map_typs_action ~neg ~pos ~ext e) cases)
  | Typed (e, ty) ->
     Typed (typed_map_typs_exp ~neg ~pos ~ext e, map_elab_typ ~neg ~pos ~ext ty)
  | Pragma _ as e -> e

and typed_map_value_binding ~pos ~ext (vb : value_binding) =
  { vb with typ = pos ~ext vb.typ }

and typed_map_typs_action ~neg ~pos ~ext { act_body; act_bindings; act_comp_bindings } =
  let act_body = typed_map_typs_exp ~neg ~pos ~ext act_body in
  let act_bindings = SymMap.map (fun (ty, r) -> map_elab_typ ~neg ~pos ~ext ty, r) act_bindings in
  { act_body; act_bindings; act_comp_bindings }

and typed_map_func_def ~neg ~pos ~ext (poly, params, psplit, ret, body) =
  let poly, ext =
    match poly with
    | None -> None, ext
    | Some bounds ->
       let ext = IArray.length bounds :: ext in
       Some (IArray.map (fun (n, b) -> n, Option.map (map_elab_typ ~pos ~neg ~ext) b) bounds), ext
  in
  let params = List.map (fun (p, ty) -> p, Option.map (map_elab_typ ~pos ~neg ~ext) ty) params in
  let ret = Option.map (map_elab_typ ~neg ~pos ~ext) ret in
  let body = typed_map_typs_action ~neg ~pos ~ext body in
  poly, params, psplit, ret, body

let wf_typed_exp env t =
  typed_map_typs_exp ~ext:[] t
    ~neg:(fun ~ext t -> wf_ntyp ~ext:(List.map (fun x -> None, x) ext) env t; t)
    ~pos:(fun ~ext t -> wf_ptyp ~ext:(List.map (fun x -> None, x) ext) env t; t)
  |> ignore

module Elaborate = struct
  let rec exp env (e : typed_exp) : exp =
    match e with
    | None, l -> None, l
    | Some e, l -> Some (exp' env e), l

  and exp' env : typed_exp' -> exp' = function
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
       Let (p, Some (typ env ty), exp env e, exp env body.act_body)
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
    |> Exp.of_record_fields

  and case env (ps, e) = (ps, exp env e.act_body)

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
           unparse_bounds ~env ~bound:(fun ~env -> typ env) bounds
         in
         env, Some poly
    in
    poly,
    List.map (fun (p, t) -> p, Option.map (typ env) t) params,
    Option.map (typ env) ret,
    exp env body.act_body

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

  let rec exp (e : typed_exp) : IRB.exp =
    match e with
    | None, _loc -> IRB.trap "type error?"
    | Some e, _loc ->
       exp' e

  and exp' : typed_exp' -> IRB.exp = function
    | Lit (l, _) -> IRB.literal l
    | Var (_, v) -> IRB.var v
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
       (let tag = Option.map IR.Symbol.of_tuple_tag tag in
        IRB.tuple tag (List.map (fun ((fn,_loc), e) -> (fn, exp e)) fields))

    | Proj (e, (field, _loc)) ->
       IRB.project (exp e) field

    | Seq (e1, e2) ->
       fun k ->
       IRB.eval_cont (exp e1) @@ fun _v ->
       exp e2 k

    | Match ((es,_loc), split, cases) ->
       fun k ->
         IRB.maybe_dup_cont ~uses:(List.length cases) k @@ fun k ->
         let actions = List.map (fun (_pats, act) -> action act k) cases |> Array.of_list in
         IRB.eval_cont_list (List.map (fun e -> exp e) es) @@ fun vals ->
         Check_pat.compile ~actions vals split

    | Let (_p, split, _ty, e, act) ->
       fun k ->
         IRB.eval_cont (exp e) @@ fun e ->
         Check_pat.compile ~actions:[| action act k |] [e] split

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

  and action (act : typed_action) k : Check_pat.compiled_action =
    let body = exp act.act_body k in
    match act.act_comp_bindings with
    | `Unused -> Act_unused
    | `Once -> Act_unshared body
    | `Shared sc -> Act_shared (body, sc)
  and func_def ((_poly,params,psplit,_ret,body) : typed_func_def) : IR.value =
    let params =
      List.map (fun (pat, _) ->
        IR.Binder.fresh ?name:(pat_name pat) ()) params
    in
    let ret = IR.Binder.fresh () in
    Lambda(params,
           ret,
           Check_pat.compile  ~actions:[| action body (IRB.Named_cont (IR.Binder.ref ret))|] (List.map IR.var params) psplit)
end
