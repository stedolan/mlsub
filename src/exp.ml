type location =
  { source : string;
    loc_start : Lexing.position;
    loc_end : Lexing.position }

type 'a loc = 'a * location

type 'a mayloc = 'a option loc

type literal = Int of int | String of string
type symbol = string loc

type field_name = Fpositional | Fnamed of symbol
type empty

(* Expressions *)

type exp = exp' mayloc and exp' =
  (* 42 or "hello" *)
  | Lit of literal loc
  (* x *)
  | Var of symbol
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
  (* e : A *)
  | Typed of exp * tyexp
  (* (e) *)
  | Parens of exp

and 'defn field =
  { f_name: field_name;
    f_type: tyexp option;
    f_defn: 'defn option }

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
  | Ttop
  | Tbot
  | Tnamed of symbol
  | Tforall of (symbol * tyexp option * tyexp option) list * tyexp
  | Trecord of record_tyexp * [`Open | `Closed]
  | Tfunc of record_tyexp * tyexp

and record_tyexp = empty field list
