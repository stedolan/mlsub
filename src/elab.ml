open Util
open Tuple_fields
open Typedefs
open Exp

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
