open PPrint
open Exp
(*open Typedefs*)

(* FIXME: precedence is fucked here. Need to insert parens *)

let string = utf8string
let indent d = nest 2 d

let op x = blank 1 ^^ x ^^ break 1

let print_lit = function
  | Int n -> string (string_of_int n)
  (* FIXME escaping *)
  | String s -> char '"' ^^ string s ^^ char '"'

let print_symbol (s, _) = string s
let print_ident (l, _) =
  let rec go =
    function
    | 0 -> empty
    | n -> string "$outer" ^^ go (n-1) in
  string l.label ^^ go l.shift

let mayloc x f = match x with
  | (None, _) -> string "??"
  | (Some s, _) -> f s

let rec print_exp e = mayloc e @@ function
  | Lit (l, _) -> print_lit l
  | Var s -> print_ident s
  | Fn (params, body) ->
     string "fn" ^^ space ^^
       print_tuple ~tcomma:false print_pat params ^^ space ^^
       braces (print_exp body)
  | Tuple t -> print_tuple ~tcomma:true print_exp t
  | App (f, args) -> print_exp f ^^ print_tuple ~tcomma:false print_exp args
  | Proj (e, f) -> print_exp e ^^ char '.' ^^ print_symbol f
  | _ -> assert false

and print_field : 'defn . ('defn -> document) -> 'defn field -> document
  = fun print_defn field ->
  match field with
  | Fpositional (None, e) ->
     print_defn e
  | Fpositional (Some ty, e) ->
     group (print_defn e ^^ blank 1 ^^ colon ^^ break 1 ^^ print_tyexp ty)
  | Fnamed (s, None, None) ->
     char '.' ^^ print_symbol s
  | Fnamed (s, Some ty, None) ->
     group (char '.' ^^ print_symbol s ^^
            op colon ^^ print_tyexp ty)
  | Fnamed (s, None, Some e) ->
     group (char '.' ^^ print_symbol s ^^
            op equals ^^ print_defn e)
  | Fnamed (s, Some ty, Some e) ->
     group (char '.' ^^ print_symbol s ^^
            op colon ^^ print_tyexp ty ^^
            op equals ^^ print_defn e)

and print_tuple : 'defn . tcomma:bool -> ('defn -> document) -> 'defn field list mayloc -> document
  = fun ~tcomma print_defn t -> mayloc t @@ function
  | [(Fpositional _) as f] when tcomma ->
     parens (print_field print_defn f ^^ comma)
  | t ->
     parens (group (indent (break 0 ^^ 
      (separate_map (comma ^^ break 1) (print_field print_defn) t)) ^^
        break 0))

and print_pat p = mayloc p @@ function
  | Pvar s -> print_symbol s
  | Ptuple ts -> print_tuple ~tcomma:true print_pat ts
  | Pparens p -> parens (print_pat p)

and print_tyexp t = mayloc t @@ function
  | Tnamed s -> print_ident s
  | Trecord (fields, `Closed) ->
     print_tuple_tyexp ~tcomma:true fields
  | Tfunc (args, ret) ->
     print_tuple_tyexp ~tcomma:false args ^^ op (string "->") ^^
       print_tyexp ret
  | Tforall _ -> assert false
  | Tparen t -> parens (print_tyexp t)
  | Tjoin (s, t) -> print_tyexp s ^^ op (string "|") ^^ print_tyexp t
  | Tmeet (s, t) -> print_tyexp s ^^ op (string "&") ^^ print_tyexp t

and print_tuple_tyexp ~tcomma t = mayloc t @@ function
  | [(TFpositional ty)] when tcomma ->
     parens (print_tyexp ty ^^ comma)
  | t ->
     let print_field = function
       | TFpositional ty ->
          print_tyexp ty
       | TFnamed (s, ty) ->
          print_symbol s ^^ op colon ^^ print_tyexp ty in
     parens (group (indent (break 0 ^^
       (separate_map (comma ^^ break 1) print_field t) ^^ break 0)))
(*
 tuple syntax:
  (f : T = e,)
  (.f : T)
  (.f)
  (.f : T as p)
  (.f : T)

  (e : T)

  (.f :


  name: pos/named

  let's skip optional for the moment


  (.f : T as p ?= default) ???
 *)

(* These names are illegal in user-entered code, and used here only
   for debugging *)
(*let tyvar_name v : symbol = "$" ^ string_of_int v.v_id*)
(*
(* Not strictly a printing function, but only useful for printing so
   it goes here *)
let rec tyexp_of_type pol { stypes; cons } =
  match cons with
  | Ident | Annih -> assert false (* what are these called again? *)
  | Func 
 *)
