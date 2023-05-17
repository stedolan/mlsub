open Tuple_fields
open Location

type 'a mayloc = 'a option loc

type literal = Int of int | String of string | Bool of bool
type symbol = string loc
type ident = ident' loc and ident' =
  { label : string; shift : int }

type tuple_tag = string loc

(* Expressions *)

type exp = exp' mayloc and exp' =
  (* 42 or "hello" *)
  | Lit of literal loc
  (* x *)
  | Var of ident
  (* fn [...](a, b, c) { ... } *)
  | Fn of func_def
  (* fn f(a, b, c) { .... }; ... *)
  | FnDef of symbol * func_def * exp
  (* f(...) *)
  | App of exp * exp tuple_fields
  (* (a, b, c) or {x: a, y, z: c}*)
  | Tuple of tuple_tag option * exp tuple_fields
  (* let a : t = ...; ... *)
  | Let of pat * tyexp option * exp * exp
  (* e; e *)
  | Seq of exp * exp
  (* a.foo *)
  | Proj of exp * symbol
  (* if a { foo } else { bar } *)
  | If of exp * exp * exp
  (* match e { p => e | ... } *)
  | Match of exp list loc * case list
  (* (e : A) *)
  | Typed of exp * tyexp
  (* @foo *)
  | Pragma of string

and case = pat list list loc * exp

and func_def = typolybounds option * parameters * tyexp option * exp

and parameters = (pat * tyexp option) tuple_fields

(* Patterns *)

and pat = pat' mayloc and pat' =
  | Pany
  | Pbind of symbol * pat
  | Ptuple of tuple_tag option * pat tuple_fields
  | Por of pat * pat

(* Type expressions *)

and tyexp = tyexp' mayloc and tyexp' =
  | Tnamed of ident
  | Tforall of typolybounds * tyexp
  | Trecord of tuple_tag option * tyexp tuple_fields
  | Tfunc of tyexp tuple_fields * tyexp
  | Tjoin of tyexp * tyexp

and typolybounds =
  (symbol * tyexp option) list


type mapper = {
  loc : mapper -> location -> location;
  exp : mapper -> exp -> exp;
  pat : mapper -> pat -> pat;
  tyexp : mapper -> tyexp -> tyexp
}
let map_exp m e = m.exp m e
let map_tyexp m t = m.tyexp m t

let mapper =
  let loc _ l = l in

  let sym r (s, sloc) = s, r.loc r sloc in

  let mayloc f recr = function
    | (None, l) -> (None, recr.loc recr l)
    | (Some x, l) -> (Some (f recr x), recr.loc recr l) in

  let fndef r (poly, args, ret, body) =
    let poly = Option.map (List.map (fun (s, t) -> (sym r s, Option.map (r.tyexp r) t))) poly in
    let args = map_fields (fun _fn (p, t) -> (r.pat r p, Option.map (r.tyexp r) t)) args in
    let ret = Option.map (r.tyexp r) ret in
    let body = r.exp r body in
    (poly, args, ret, body)
  in

  let case r ((pats, ploc), exp) = ((List.map (List.map (r.pat r)) pats, r.loc r ploc), r.exp r exp) in

  let exp = mayloc @@ fun r e -> match e with
    | Lit (l, loc) ->
       Lit (l, r.loc r loc)
    | Var (n, loc) ->
       Var (n, r.loc r loc)
    | Fn def ->
       Fn (fndef r def)
    | FnDef (s, def, body) ->
       FnDef (sym r s, fndef r def, r.exp r body)
    | App (f, args) ->
       App (r.exp r f, map_fields (fun _fn e -> r.exp r e) args)
    | Tuple (tag, es) ->
       Tuple (Option.map (sym r) tag, map_fields (fun _fn e -> r.exp r e) es)
    | Let (p, ty, e, body) ->
       Let (r.pat r p, Option.map (r.tyexp r) ty, r.exp r e, r.exp r body)
    | Seq (e1, e2) ->
       Seq (r.exp r e1, r.exp r e2)
    | Proj (e, s) ->
       Proj (r.exp r e, sym r s)
    | If (e, et, ef) ->
       If (r.exp r e, r.exp r et, r.exp r ef)
    | Typed (e, t) ->
       Typed (r.exp r e, r.tyexp r t)
    | Match ((e, eloc), cases) ->
       Match ((List.map (r.exp r) e, r.loc r eloc), List.map (case r) cases)
    | Pragma s ->
       Pragma s
  in

  let pat = mayloc @@ fun r p -> match p with
    | Pany -> Pany
    | Pbind (s, p) -> Pbind (sym r s, r.pat r p)
    | Ptuple (tag, ps) ->
       Ptuple (Option.map (sym r) tag, map_fields (fun _fn x -> r.pat r x) ps)
    | Por (p, q) -> Por (r.pat r p, r.pat r q)
  in

  let tyexp = mayloc @@ fun r t -> match t with
    | Tnamed (n,l) ->
       Tnamed (n, r.loc r l)
    | Tforall (bounds, body) ->
       let bounds = List.map (fun (s, t) -> (sym r s, Option.map (r.tyexp r) t)) bounds in
       let body = r.tyexp r body in
       Tforall (bounds, body)
    | Trecord (tag, ts) ->
       Trecord (Option.map (sym r) tag, map_fields (fun _fn t -> r.tyexp r t) ts)
    | Tfunc (args, ret) ->
       Tfunc (map_fields  (fun _fn t -> r.tyexp r t) args, r.tyexp r ret)
    | Tjoin (s, t) ->
       Tjoin (r.tyexp r s, r.tyexp r t)
  in
  { loc; exp; pat; tyexp }

let strip_locations =
  { mapper with loc = fun _ _ -> noloc }

let equal e1 e2 = map_exp strip_locations e1 = map_exp strip_locations e2
  
