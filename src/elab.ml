(*
open Tuple_fields
open Typedefs
open Exp

(* pottier-style applicative functor for elaboration *)
type _ elab_req =
  | Unit : unit elab_req
  | Pair : 's elab_req * 't elab_req -> ('s * 't) elab_req
  | Typ : polarity * typ -> tyexp elab_req
  | Gen :
      { pol : polarity;
        bounds : (string option * styp * styp) array;
        flow : Flow_graph.t;
        body : 'a elab_req } ->
      (typolybounds * 'a) elab_req
type +'a elab =
  | Elab : 'r elab_req * ('r -> 'a) -> 'a elab

let elab_pure x = Elab (Unit, fun () -> x)
let elab_map g (Elab (r, f)) = Elab (r, fun x -> g (f x))
let elab_pair (Elab (a, f)) (Elab (b, g)) = Elab (Pair (a, b), fun (a, b) -> f a, g b)
let elab_typ pol ty = Elab (Typ (pol, ty), fun x -> x)

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

let rec map_free_elab_req : type a . _ -> _ -> _ -> a elab_req -> a elab_req =
  fun lvl ix rw rq -> match rq with
  | Unit -> Unit
  | Pair (s, t) ->
     Pair (map_free_elab_req lvl ix rw s,
           map_free_elab_req lvl ix rw t)
  | Typ (pol, t) ->
     Typ (pol, map_free_typ lvl ix rw pol t)
  | Gen { pol; bounds; flow; body } ->
     let ix = ix + 1 in
     let bounds =
       Array.map (fun (name, l, u) ->
         name,
         map_free_styp lvl ix rw pol l,
         map_free_styp lvl ix rw (polneg pol) u) bounds in
     let body = map_free_elab_req lvl ix rw body in
     Gen { pol; bounds; flow; body }

let rec map_bound_elab_req : type a . _ -> _ -> _ -> a elab_req -> a elab_req =
  fun sort ix rw rq -> match rq with
  | Unit -> Unit
  | Pair (s, t) ->
     Pair (map_bound_elab_req sort ix rw s,
           map_bound_elab_req sort ix rw t)
  | Typ (pol, t) ->
     Typ (pol, map_bound_typ sort ix rw pol t)
  | Gen { pol; bounds; flow; body } ->
     let ix = ix + 1 in
     let bounds =
       Array.map (fun (name, l, u) ->
         name,
         map_bound_styp sort ix rw pol l,
         map_bound_styp sort ix rw (polneg pol) u) bounds in
     let body = map_bound_elab_req sort ix rw body in
     Gen { pol; bounds; flow; body }

let rec wf_elab_req : type a . _ -> a elab_req -> unit =
  fun env rq -> match rq with
  | Unit -> ()
  | Pair (s, t) ->
     wf_elab_req env s;
     wf_elab_req env t
  | Typ (pol, t) ->
     wf_typ pol env t
  | Gen { pol; bounds; flow; body } ->
     (* toplevel references to bound variables should be in flow, not bounds *)
     bounds |> Array.iter (fun (_name, p, n) ->
       assert (p.bound = []); assert (n.bound = []));
     let env, _, inst = enter_poly' pol env SymMap.empty bounds flow in
     let body = map_bound_elab_req (binder_sort pol) 0 inst body in
     wf_elab_req env body


let rec elaborate : type a . Type_print.nenv -> a elab_req -> a =
  fun env rq -> match rq with
  | Unit -> ()
  | Pair (s, t) -> (elaborate env s, elaborate env t)
  | Typ (pol, t) -> Type_print.convert env pol t
  | Gen { pol; bounds; flow; body } ->
     let env, constraints, inst = Type_print.enter_poly_for_convert env pol bounds flow in
     let body = map_bound_elab_req (binder_sort pol) 0 inst body in
     constraints, elaborate env body

let elaborate env (Elab (rq, k)) = k (elaborate env rq)

open PPrint
let rec pr_elab_req : type a . a elab_req -> document = function
  | Unit -> empty
  | Pair (s, t) -> pr_elab_req s ^^ pr_elab_req t
  | Typ (pol, t) -> pr_typ pol t ^^ hardline
  | Gen {pol; bounds=_; flow=_; body} ->
     utf8string "∀" ^^ (match pol with Pos -> utf8string "⁺" | Neg -> utf8string "⁻") ^^ nest 2 (hardline ^^ pr_elab_req body)

*)
