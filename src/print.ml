open PPrint
open Exp
(*open Typedefs*)

(* FIXME: precedence is fucked here. Need to insert parens *)

let string = utf8string
let indent d = nest 2 d

let op x = blank 1 ^^ x ^^ break 1

let print_lit = function
  | Bool b -> string (string_of_bool b)
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

let parens x = parens (group x)

let rec print_exp e = mayloc e @@ function
  | Lit (l, _) -> print_lit l
  | Var s -> print_ident s
  | Fn (params, body) ->
     string "fn" ^^ space ^^
       print_fields print_pat params ^^ space ^^
       braces (print_exp body)
  | Tuple t -> print_tuple print_exp t
  | App (f, args) -> print_exp f ^^ print_fields print_exp args
  | Proj (e, f) -> print_exp e ^^ char '.' ^^ print_symbol f
  | If (e, t, f) ->
     string "if" ^^ break 1 ^^ print_exp e ^^
       braces (print_exp t) ^^ op (string "else") ^^
         braces (print_exp f)
  | Typed (e, t) -> parens (print_exp e ^^ op (char ':') ^^ print_tyexp t)
  | Parens e -> parens (print_exp e)
  | Pragma s -> char '@' ^^ string s
  | _ -> assert false

and print_pos_field : 'defn . ('defn -> document) -> 'defn * tyexp option -> document
  = fun print_defn (e, ty) ->
    match ty with
    | None -> print_defn e
    | Some ty -> 
       group (print_defn e ^^ blank 1 ^^ colon ^^ break 1 ^^ print_tyexp ty)

and print_fields' : 'defn . ('defn -> document) -> 'defn fields -> document
  = fun print_defn {fields_pos; fields_named; fields_open} ->
  let fields_pos = fields_pos |> List.map (print_pos_field print_defn) in
  let fields_named = fields_named |> List.map (function
    | (s, None, None) ->
       char '.' ^^ print_symbol s
    | (s, None, Some ty) ->
       group (char '.' ^^ print_symbol s ^^
                op colon ^^ print_tyexp ty)
    | (s, Some e, None) ->
       group (char '.' ^^ print_symbol s ^^
                op equals ^^ print_defn e)
    | (s, Some e, Some ty) ->
       group (char '.' ^^ print_symbol s ^^
              op colon ^^ print_tyexp ty ^^
              op equals ^^ print_defn e)) in
  let fields_open = match fields_open with `Open -> [string "..."] | `Closed -> [] in
  parens (group (indent (break 0 ^^ 
     (separate (comma ^^ break 1) (fields_pos @ fields_named @ fields_open))) ^^
       break 0))

and print_fields : 'defn . ('defn -> document) -> 'defn fields -> document
  = fun print_defn t -> print_fields' print_defn t

(* print_tuple: print a trailing comma on a single position elem *)
and print_tuple : 'defn . ('defn -> document) -> 'defn fields -> document
  = fun print_defn t -> match t with
  | {fields_pos = [f]; fields_named = []; fields_open = `Closed} ->
     parens (print_pos_field print_defn f ^^ comma)
  | t -> print_fields' print_defn t

and print_pat p = mayloc p @@ function
  | Pvar s -> print_symbol s
  | Ptuple ts -> print_tuple print_pat ts
  | Pparens p -> parens (print_pat p)
  | Ptyped (p, ty) -> parens (print_pat p ^^ op (string ":") ^^ print_tyexp ty)

and print_tyexp t = mayloc t @@ function
  | Tnamed s -> print_ident s
  | Trecord fields ->
     print_tyexp_tuple fields
  | Tfunc (args, ret) ->
     print_tyexp_fields args ^^ op (string "->") ^^
       print_tyexp ret
  | Tforall _ -> assert false
  | Tparen t -> parens (print_tyexp t)
  | Tjoin (s, t) -> print_tyexp s ^^ op (string "|") ^^ print_tyexp t
  | Tmeet (s, t) -> print_tyexp s ^^ op (string "&") ^^ print_tyexp t

and print_tyexp_fields' { tyfields_pos; tyfields_named; tyfields_open } =
  let tyfields_pos = tyfields_pos |> List.map print_tyexp in
  let tyfields_named = tyfields_named |> List.map (fun (s, ty) ->
    print_symbol s ^^ op colon ^^ print_tyexp ty) in
  let tyfields_open = match tyfields_open with `Open -> [string "..."] | `Closed -> [] in
  parens (group (indent (break 0 ^^ separate (comma ^^ break 1)
                  (tyfields_pos @ tyfields_named @ tyfields_open))))

and print_tyexp_fields t = print_tyexp_fields' t
and print_tyexp_tuple t = match t with
  | {tyfields_pos = [f]; tyfields_named = []; tyfields_open = `Closed} ->
    parens (print_tyexp f ^^ comma)
  | t -> print_tyexp_fields' t

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
