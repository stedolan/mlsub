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
  (* @foo *)
  | Pragma of string

and 'defn fields =
  { fields_pos : ('defn * tyexp option) list;
    fields_named : (symbol * 'defn option * tyexp option) list;
    fields_open : [`Open|`Closed] }

and tuple = exp fields

(* Patterns *)

and pat = pat' mayloc and pat' =
  | Ptuple of tuple_pat
  | Pvar of symbol
  | Pparens of pat

and tuple_pat = pat fields

(* Type expressions *)

and tyexp = tyexp' mayloc and tyexp' =
  | Tnamed of ident
  | Tforall of (symbol * tyexp option * tyexp option) list * tyexp
  | Trecord of tyexp_fields
  | Tfunc of tyexp_fields * tyexp
  | Tparen of tyexp
  | Tjoin of tyexp * tyexp
  | Tmeet of tyexp * tyexp

and 'defn field_tyexp =
  | TFpositional of 'defn
  | TFnamed of symbol * 'defn

and tyexp_fields =
  { tyfields_pos : tyexp list;
    tyfields_named : (symbol * tyexp) list;
    tyfields_open : [`Open|`Closed] }
