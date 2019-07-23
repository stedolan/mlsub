open PPrint
open Exp

let string = utf8string
let indent d = nest 2 d

let op x = blank 1 ^^ x ^^ break 1

let print_lit = function
  | Int n -> string (string_of_int n)
  (* FIXME escaping *)
  | String s -> char '"' ^^ string s ^^ char '"'

let print_symbol (s, _) = string s

let mayloc x f = match x with
  | (None, _) -> string "??"
  | (Some s, _) -> f s

let rec print_exp e = mayloc e @@ function
  | Lit (l, _) -> print_lit l
  | Var (s, _) -> string s
  | Fn (params, body) ->
     string "fn" ^^ space ^^
       print_tuple ~tcomma:false print_pat params ^^ space ^^
       braces (print_exp body)
  | Tuple t -> print_tuple ~tcomma:true print_exp t
  | App (f, args) -> print_exp f ^^ print_tuple ~tcomma:false print_exp args
  | _ -> assert false

and print_field : 'defn . ('defn -> document) -> 'defn field -> document
  = fun print_defn { f_name; f_type; f_defn } ->
  match f_name, f_type, f_defn with
  | Fpositional, None, None ->
     assert false
  | Fpositional, Some t, None ->
     print_tyexp t
  | Fpositional, None, Some e ->
     print_defn e
  | Fpositional, Some ty, Some e ->
     group (print_defn e ^^ blank 1 ^^ colon ^^ break 1 ^^ print_tyexp ty)
  | Fnamed s, None, None ->
     char '.' ^^ print_symbol s
  | Fnamed s, Some ty, None ->
     group (char '.' ^^ print_symbol s ^^
            op colon ^^ print_tyexp ty)
  | Fnamed s, None, Some e ->
     group (char '.' ^^ print_symbol s ^^
            op equals ^^ print_defn e)
  | Fnamed s, Some ty, Some e ->
     group (char '.' ^^ print_symbol s ^^
            op colon ^^ print_tyexp ty ^^
            op equals ^^ print_defn e)

and print_tuple : 'defn . tcomma:bool -> ('defn -> document) -> 'defn field list mayloc -> document
  = fun ~tcomma print_defn t -> mayloc t @@ function
  | [{f_name = Fpositional; _} as f] when tcomma ->
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
  (* FIXME: pick good names for top and bottom *)
  | Ttop -> string "any"
  | Tbot -> string "never"
  | Tnamed s -> print_symbol s
  | _ -> assert false

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

