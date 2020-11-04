open Tuple_fields

type location =
  { source : string;
    loc_start : Lexing.position;
    loc_end : Lexing.position }

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
  (* fn (a, b, c) { ... } *)
  | Fn of typed_pats * tyexp option * exp
  (* fn f(a, b, c) { .... }; ... *)
  (* | Def of symbol * typed_pats * exp * exp *)
  (* f(...) *)
  | App of exp * (exp option) tuple_fields
  (* (a, b, c) *)
  | Tuple of tuple
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

and typed_pats = (pat option * tyexp option) tuple_fields

and tuple = (exp option * tyexp option) tuple_fields

(* Patterns *)

and pat = pat' mayloc and pat' =
  | Ptuple of pat option tuple_fields
  | Pvar of symbol
  | Pparens of pat

(* Type expressions *)

and tyexp = tyexp' mayloc and tyexp' =
  | Tnamed of ident
  | Tforall of (symbol * ([`Sub|`Sup] * tyexp) option) list * tyexp
  | Trecord of tyexp tuple_fields
  | Tfunc of tyexp tuple_fields * tyexp
  | Tparen of tyexp
  | Tjoin of tyexp * tyexp
  | Tmeet of tyexp * tyexp
