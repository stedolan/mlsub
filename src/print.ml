open PPrint
open Tuple_fields
open Exp

(* FIXME: precedence is fucked here. Need to insert parens *)

let string = utf8string
let indent d = nest 2 d

let op x = blank 1 ^^ string x ^^ break 1

let literal = function
  | Bool b -> string (string_of_bool b)
  | Int n -> string (string_of_int n)
  (* FIXME escaping *)
  | String s -> char '"' ^^ string s ^^ char '"'

let symbol (s, _) = string s
let ident (l, _) =
  let rec go =
    function
    | 0 -> empty
    | n -> string "$outer" ^^ go (n-1) in
  string l.label ^^ go l.shift

let mayloc x f = match x with
  | (None, _) -> string "<err>"
  | (Some s, _) -> f s

let parens x = parens (group x)
let braces x = braces (group x)
let brackets x = brackets (group x)

let sep ?(trail=false) s xs =
  group (indent (break 0 ^^ separate_map (s ^^ break 1) group xs) ^^
           (if trail then s else empty) ^^
           break 0)

let rec exp e = mayloc e @@ function
  | Lit (l, _) -> literal l
  | Var s -> ident s
  | Fn (poly, params, ty, body) ->
     string "fn" ^^ space ^^
       (match poly with
        | None -> empty
        | Some poly -> typolybounds poly) ^^
       parens (fields parameter params) ^^
       (match ty with
        | None -> empty
        | Some ty -> blank 1 ^^ string "->" ^^ blank 1 ^^ tyexp ty) ^^
       space ^^ braces (break 1 ^^ exp body ^^ break 1)
  | Let (p, ty, e, body) ->
     group (string "let" ^^ space ^^
       pat p ^^ opt_type_annotation ty ^^
       op "=" ^^ group (exp e) ^^
       string ";") ^^ break 1 ^^ exp body
  | Tuple t -> record ~pun:exp_pun exp t
  | App (f, args) ->
     exp f ^^
     parens (fields argument args)
  | Proj (e, f) -> exp e ^^ char '.' ^^ field_name (Field_named (fst f))
  | If (e, t, f) ->
     string "if" ^^ blank 1 ^^ exp e ^^
       braces (exp t) ^^ op "else" ^^
         braces (exp f)
  | Typed (e, t) -> parens (exp e ^^ opt_type_annotation (Some t))
  | Parens e -> parens (exp e)
  | Pragma s -> char '@' ^^ string s

and fields : 'e . ?tcomma:bool -> (pos:bool -> field_name -> 'e -> document) -> 'e tuple_fields -> document =
  fun ?(tcomma=false) print_elem {fnames; fields; fopen} ->
  let rec annot_fnames i = function
    | (Field_positional n as fn) :: rest when n = i ->
       (true, fn) :: annot_fnames (i+1) rest
    | fnames -> List.map (fun fn -> false, fn) fnames in
  let fnames = annot_fnames 0 fnames in
  let tcomma = tcomma && List.length fnames = 1 && fopen = `Closed in
  sep comma ~trail:tcomma
    (List.map (fun (pos,f) -> print_elem ~pos f (FieldMap.find f fields)) fnames
    @ (match fopen with `Open -> [string "..."] | `Closed -> []))

and record : 'e . pun:(field_name * 'e -> bool) -> ('e -> document) -> 'e tuple_fields -> document =
  fun ~pun print_elem t ->
  if t.fnames = List.init (List.length t.fnames) (fun i -> Field_positional i) then
    parens (fields ~tcomma:true (fun ~pos:_ _ e -> print_elem e) t)
  else
    braces (fields (fun ~pos:_ fn e ->
       if pun (fn, e) then field_name fn else
          field_name fn ^^ string ":" ^^ break 1 ^^ print_elem e) t)

and field_name = function
  (* FIXME: positional field syntax *)
  | Field_positional n -> string (Printf.sprintf ".%d" n)
  | Field_named s -> string s

and exp_pun = function
  | Field_named s, (Some (Var ({label=s';shift=0}, _)), _) -> s = s'
  | _ -> false
and pat_pun = function
  | Field_named s, (Some (Pvar (s',_)), _) -> s = s'
  | _ -> false

and argument ~pos fn arg =
  match fn, arg with
  | _ when pos -> exp arg
  | Field_named s, (Some (Var ({label=s';shift=0}, _)), _) when s = s' ->
     string "~" ^^ field_name fn
  | fn, arg ->
     string "~" ^^ field_name fn ^^ colon ^^ space ^^ exp arg

and parameter ~pos fn (p,ty) =
  match fn, p with
  | _ when pos -> pat p ^^ opt_type_annotation ~prespace:false ty
  | Field_named s, (Some (Pvar (s',_)), _) when s = s' ->
     string "~" ^^ field_name fn ^^
       opt_type_annotation ty
  | _ ->
     string "~" ^^ field_name fn ^^ space ^^ pat p ^^
       opt_type_annotation ty

and opt_type_annotation ?(prespace=true) = function
  | Some ty -> (if prespace then blank 1 else empty) ^^ string ":" ^^ blank 1 ^^ tyexp ty
  | None -> empty

and pat p = mayloc p @@ function
  | Pvar s -> symbol s
  | Ptuple ts -> record ~pun:pat_pun pat ts
  | Pparens p -> parens (pat p)

and tyexp t = mayloc t @@ function
  | Tnamed s -> ident s
  | Trecord fields ->
     record ~pun:(fun _ -> false) tyexp fields
  | Tfunc (args, ret) ->
     parens (fields argtype args) ^^ op "->" ^^
       tyexp ret
  | Tforall (bounds, body) ->
      typolybounds bounds ^^ space ^^ tyexp body
  | Tparen t -> parens (tyexp t)
  | Tjoin (s, t) -> tyexp s ^^ op "|" ^^ tyexp t

and argtype ~pos fn ty =
  if pos then tyexp ty
  else string "~" ^^ field_name fn ^^ colon ^^ space ^^ tyexp ty

and typolybounds bs =
  let bound = function
    | (a, None) -> symbol a
    | (a, Some ty ) ->
       symbol a ^^ op "<:" ^^ tyexp ty in
  brackets (separate (comma ^^ break 1) (List.map bound bs))
