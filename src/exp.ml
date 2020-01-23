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
  | Fn of tuple_pat * exp
  (* fn f(a, b, c) { .... }; ... *)
  | Def of symbol * tuple_pat * exp * exp
  (* f(...) *)
  | App of exp * tuple
  (* (a, b, c) *)
  | Tuple of tuple
  (* let (a, b, c) = ...; ... *)
  | Let of tuple_pat * exp * exp
  (* a.foo *)
  | Proj of exp * symbol
  (* if a { foo } else { bar } *)
  | If of exp * exp * exp
  (* (e : A) *)
  | Typed of exp * tyexp
  (* (e) *)
  | Parens of exp

and 'defn field =
  | Fpositional of tyexp option * 'defn
  | Fnamed of symbol * tyexp option * 'defn option

and tuple = tuple' mayloc and tuple' =
  exp field list

(* Patterns *)

and pat = pat' mayloc and pat' =
  | Ptuple of tuple_pat
  | Pvar of symbol
  | Pparens of pat

and tuple_pat = tuple_pat' mayloc and tuple_pat' =
  pat field list

(* Type expressions *)

and tyexp = tyexp' mayloc and tyexp' =
  | Tnamed of ident
  | Tforall of (symbol * tyexp option * tyexp option) list * tyexp
  | Trecord of tuple_tyexp * [`Closed|`Open]
  | Tfunc of tuple_tyexp * tyexp
  | Tparen of tyexp
  | Tjoin of tyexp * tyexp
  | Tmeet of tyexp * tyexp

and 'defn field_tyexp =
  | TFpositional of 'defn
  | TFnamed of symbol * 'defn

and tuple_tyexp = tuple_tyexp' mayloc and tuple_tyexp'=
  tyexp field_tyexp list
