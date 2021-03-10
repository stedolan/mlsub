open Tuple_fields

type location =
  { source : string;
    loc_start : Lexing.position;
    loc_end : Lexing.position }

let noloc =
  let loc : Lexing.position = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0} in
  { source = "_"; loc_start = loc; loc_end = loc}

type 'a loc = 'a * location

type 'a mayloc = 'a option loc

type literal = Int of int | String of string | Bool of bool
type symbol = string loc
type ident = ident' loc and ident' =
  { label : string; shift : int }

(* Expressions *)

type exp = exp' mayloc and exp' =
  (* 42 or "hello" *)
  | Lit of literal loc
  (* x *)
  | Var of ident
  (* fn [...](a, b, c) { ... } *)
  | Fn of typolybounds option * parameters * tyexp option * exp
  (* fn f(a, b, c) { .... }; ... *)
  (* | Def of symbol * typed_pats * exp * exp *)
  (* f(...) *)
  | App of exp * exp tuple_fields
  (* (a, b, c) or {x: a, y, z: c}*)
  | Tuple of exp tuple_fields
  (* let a : t = ...; ... *)
  | Let of pat * tyexp option * exp * exp
  (* a.foo *)
  | Proj of exp * symbol
  (* if a { foo } else { bar } *)
  | If of exp * exp * exp
  (* (e : A) *)
  | Typed of exp * tyexp
  (* (e) *)
  | Parens of exp
  (* @foo *)
  | Pragma of string

and parameters = (pat * tyexp option) tuple_fields

(* Patterns *)

and pat = pat' mayloc and pat' =
  | Ptuple of pat tuple_fields
  | Pvar of symbol
  | Pparens of pat

(* Type expressions *)

and tyexp = tyexp' mayloc and tyexp' =
  | Tnamed of ident
  | Tforall of typolybounds * tyexp
  | Trecord of tyexp tuple_fields
  | Tfunc of tyexp tuple_fields * tyexp
  | Tparen of tyexp
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


let mapper =
  let loc _ l = l in

  let sym r (s, sloc) = s, r.loc r sloc in

  let mayloc f recr = function
    | (None, l) -> (None, recr.loc recr l)
    | (Some x, l) -> (Some (f recr x), recr.loc recr l) in

  let exp = mayloc @@ fun r e -> match e with
    | Lit (l, loc) ->
       Lit (l, r.loc r loc)
    | Var (n, loc) ->
       Var (n, r.loc r loc)
    | Fn (poly, args, ret, body) ->
       let poly = Option.map (List.map (fun (s, t) -> (sym r s, Option.map (r.tyexp r) t))) poly in
       let args = map_fields (fun _fn (p, t) -> (r.pat r p, Option.map (r.tyexp r) t)) args in
       let ret = Option.map (r.tyexp r) ret in
       let body = r.exp r body in
       Fn (poly, args, ret, body)
    | App (f, args) ->
       App (r.exp r f, map_fields (fun _fn e -> r.exp r e) args)
    | Tuple es ->
       Tuple (map_fields (fun _fn e -> r.exp r e) es)
    | Let (p, ty, e, body) ->
       Let (r.pat r p, Option.map (r.tyexp r) ty, r.exp r e, r.exp r body)
    | Proj (e, s) ->
       Proj (r.exp r e, sym r s)
    | If (e, et, ef) ->
       If (r.exp r e, r.exp r et, r.exp r ef)
    | Typed (e, t) ->
       Typed (r.exp r e, r.tyexp r t)
    | Parens e ->
       Parens (r.exp r e)
    | Pragma s ->
       Pragma s
  in

  let pat = mayloc @@ fun r p -> match p with
    | Ptuple ps -> Ptuple (map_fields (fun _fn x -> r.pat r x) ps)
    | Pvar s -> Pvar (sym r s)
    | Pparens p -> Pparens (r.pat r p)
  in

  let tyexp = mayloc @@ fun r t -> match t with
    | Tnamed (n,l) ->
       Tnamed (n, r.loc r l)
    | Tforall (bounds, body) ->
       let bounds = List.map (fun (s, t) -> (sym r s, Option.map (r.tyexp r) t)) bounds in
       let body = r.tyexp r body in
       Tforall (bounds, body)
    | Trecord ts ->
       Trecord (map_fields (fun _fn t -> r.tyexp r t) ts)
    | Tfunc (args, ret) ->
       Tfunc (map_fields  (fun _fn t -> r.tyexp r t) args, r.tyexp r ret)
    | Tparen t ->
       Tparen (r.tyexp r t)
    | Tjoin (s, t) ->
       Tjoin (r.tyexp r s, r.tyexp r t)
  in
  { loc; exp; pat; tyexp }

let strip_locations =
  { mapper with loc = fun _ _ -> noloc }

let equal e1 e2 = map_exp strip_locations e1 = map_exp strip_locations e2

let self_delimiting_tyexp = function
  | Tparen _ | Tnamed _ | Trecord _ -> true
  | _ -> false

let normalise =
  let tyexp r = function
    | Some (Tjoin (s, t)), loc ->
       let s =
         match r.tyexp r s with
         | Some (Tparen _ | Tnamed _ | Trecord _ | Tjoin _), _ -> s
         | _, loc -> Some (Tparen s), loc in
       let t =
         match r.tyexp r t with
         | Some (Tnamed _ | Trecord _ | Tjoin _), _ -> t
         | _, loc -> Some (Tparen t), loc in
       Some (Tjoin (s, t)), loc
    | t -> mapper.tyexp r t in
  { mapper with tyexp }
  
