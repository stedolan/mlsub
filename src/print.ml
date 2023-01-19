open PPrint
open Tuple_fields
open Exp
open Util

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

let qsymbol s = char '\'' ^^ symbol s

let ident (l, _) =
  let rec go =
    function
    | 0 -> empty
    | n -> string "$outer" ^^ go (n-1) in
  string l.label ^^ go l.shift

let mayloc x f = match x with
  | (None, _) -> string "<err>"
  | (Some s, _) -> f s

let braces' = braces
let parens x = parens (group x)
let braces x = braces (group x)
let brackets x = brackets (group x)

let sep ?(trail=false) s xs =
  group (indent (break 0 ^^ separate_map (s ^^ break 1) group xs) ^^
           (if trail then s else empty) ^^
           break 0)
let pp_doc () d = d
let rec exp e = mayloc e @@ function
  | Lit (l, _) -> literal l
  | Var s -> ident s
  | Fn def -> fndef ~name:None def
  | FnDef (s, def, body) ->
     fndef ~name:(Some s) def ^^ break 1 ^^ exp body
  | Seq (e1, e2) ->
     PPFmt.pp "@[%a;@]@ %a" pp_doc (exp e1) pp_doc (exp e2)
     (* group (exp e1 ^^ semi) ^^ break 1 ^^ exp e2 *)
  | Let (p, ty, e, body) ->
     PPFmt.pp "@[let %a%a =@ @[%a@];@]@ %a"
       (fun () d -> d) (pat p)
       (fun () d -> d) (opt_type_annotation ty)
       (fun () d -> d) (exp e)
       (fun () d -> d) (exp body)
(*
     group (string "let" ^^ space ^^
       pat p ^^ opt_type_annotation ty ^^
       op "=" ^^ group (exp e) ^^
       string ";") ^^ break 1 ^^ exp body*)
  | Tuple (None, t) -> record ~tcomma:true ~pun:exp_pun exp t
  | Tuple (Some tag, t) when Tuple_fields.is_empty t -> symbol tag
  | Tuple (Some tag, t) -> symbol tag ^^ record ~tcomma:false ~pun:exp_pun exp t
  | App (f, args) ->
     exp f ^^
     parens (fields argument args)
  | Proj (e, f) -> exp e ^^ char '.' ^^ field_name (Field_named (fst f))
  | If (e, t, f) ->
     string "if" ^^ blank 1 ^^ exp e ^^ block t ^^ blank 1 ^^ string "else" ^^ block f
  | Match (e, cs) ->
     string "match" ^^ blank 1 ^^ separate_map (comma ^^ break 1) exp e ^^ space ^^
       braces' (indent (break 1 ^^ cases cs) ^^ break 1)
  | Typed (e, t) -> parens (exp e ^^ opt_type_annotation (Some t))
  | Parens e -> parens (exp e)
  | Pragma s -> char '@' ^^ string s

and fndef ~name (poly, params, ty, body) =
  group (
    string "fn" ^^ space ^^
      (match name with None -> empty | Some s -> symbol s) ^^
      (match poly with
      | None -> empty
      | Some poly -> typolybounds poly) ^^
     parens (fields parameter params) ^^
     (match ty with
      | None -> empty
      | Some ty ->
         indent (blank 1 ^^ group (string "->" ^^ break 1 ^^ group (tyexp ty))))) ^^
    block body

and block e =
  space ^^ braces' (indent (break 1 ^^ exp e) ^^ break 1)

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

and record : 'e . tcomma:bool -> pun:(field_name * 'e -> bool) -> ('e -> document) -> 'e tuple_fields -> document =
  fun ~tcomma ~pun print_elem t ->
  if t.fnames = List.init (List.length t.fnames) (fun i -> Field_positional i) then
    parens (fields ~tcomma (fun ~pos:_ _ e -> print_elem e) t)
  else
    braces (fields ~tcomma:false (fun ~pos:_ fn e ->
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
  | Some ty -> (if prespace then blank 1 else empty) ^^ string ":" ^^ blank 1 ^^ group (tyexp ty)
  | None -> empty

and cases cs =
  cs |> separate_map (break 1) @@ fun (pps, e) ->
    (pps |> separate_map (break 1) @@ fun ps ->
      string "| " ^^ group (separate_map (comma ^^ break 1) pat ps))
    ^^ op "=>" ^^ exp e

and pat p = mayloc p @@ function
  | Pany -> string "_"
  | Pvar s -> symbol s
  | Ptuple (None, ts) -> record ~tcomma:true ~pun:pat_pun pat ts
  | Ptuple (Some tag, ts) when Tuple_fields.is_empty ts -> symbol tag
  | Ptuple (Some tag, ts) -> symbol tag ^^ record ~tcomma:false ~pun:pat_pun pat ts
  | Por (p, q) -> pat p ^^ op "|" ^^ pat q
  | Pparens p -> parens (pat p)

and tyexp t = mayloc t @@ function
  | Tnamed s -> ident s
  | Trecord (None, fields) ->
     record ~tcomma:true ~pun:(fun _ -> false) tyexp fields
  | Trecord (Some tag, fields) when Tuple_fields.is_empty fields ->
     qsymbol tag
  | Trecord (Some tag, fields) ->
     qsymbol tag ^^ record ~tcomma:false ~pun:(fun _ -> false) tyexp fields
  | Tfunc (args, ret) ->
     parens (fields argtype args) ^^
       space ^^ group (string "->" ^^ break 1 ^^ group (tyexp ret))
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
       group (symbol a ^^ op "<:" ^^ tyexp ty) in
  brackets (separate (comma ^^ break 1) (List.map bound bs))
