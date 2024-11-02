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

type precedence =
  | Term
  | Infix
  | Exp
  | Max

let precedence : exp' -> precedence = function
  | Lit _
  | Var _
  | Pragma _
  | App _
  | Proj _
  | Tuple _
  | Typed _ -> Term
  | Seq _ | Let _ | FnDef _
  | Fn _ -> Exp
  | If _ | Match _ -> Term

let ty_precedence : tyexp' -> precedence = function
  | Ttyvar _ | Ttop | Tbot -> Term
  | Trecord (Some (Named_tag ("_", _)), [], _) -> Infix
  | Trecord (_,_,Ftuple _) -> Term
  | Trecord (_,_,Frecord _) -> Infix
  | Tjoin _ -> Infix
  | _ -> Exp

let pat_precedence : pat' -> precedence = function
  | Pany | Ptuple _ -> Term
  | Pbind (_, (Some Pany, _)) -> Term
  | Pbind _ | Por _ -> Infix

let sep ?(trail=false) s xs =
  group (indent (break 0 ^^ separate_map (s ^^ break 1) group xs) ^^
           (if trail then s else empty) ^^
           break 0)
let pp_doc () d = d

let field_name = function
  | Field_positional n -> string (Printf.sprintf "%d" n)
  | Field_named s -> string s

let fields ~tcomma f = function
  | Ftuple [x] when tcomma ->
     (* Trailing comma required to disambiguate *)
     parens (sep ~trail:true comma [f x])
  | Ftuple fs ->
     let fs = List.map f fs in
     parens (sep comma fs)
  | Frecord fs ->
     let mand_flag = function
       | Mandatory -> empty
       | Optional -> string "?"
     in
     let fs = List.map (function
       | ((s,_loc), m, Some x) -> field_name s ^^ mand_flag m ^^ string ":" ^^ break 1 ^^ f x
       | ((s,_loc), m, None) -> field_name s ^^ mand_flag m) fs in
     braces (sep (ifflat comma empty) fs)

(* FIXME syntax *)
let tuple_tag = function
  | Anon_tag -> string "#"
  | Struct_tag t -> string "#" ^^ symbol t
  | Named_tag t -> symbol t

let rec exp ~prec e =
  match e with
  | None, _ -> string "(<err>)"
  | Some e, _ ->
    let doc = exp_ e in
    if precedence e > prec then parens doc else doc

and exp_ e =
  let prec = precedence e in
  match e with
  | Lit (l, _) -> literal l
  | Var s -> ident s
  | Fn def -> fndef ~name:None def
  | FnDef (s, def, body) ->
     fndef ~name:(Some s) def ^^ break 1 ^^ exp ~prec:Exp body
  | Seq (e1, e2) ->
     PPFmt.pp "@[%a;@]@ %a" pp_doc (exp ~prec e1) pp_doc (exp ~prec e2)
     (* group (exp e1 ^^ semi) ^^ break 1 ^^ exp e2 *)
  | Let (p, ty, e, body) ->
     PPFmt.pp "@[let %a =@ @[%a@];@]@ %a"
       (fun () d -> d) (group (pat ~prec:Term p ^^ opt_type_annotation ty))
       (fun () d -> d) (exp ~prec e)
       (fun () d -> d) (exp ~prec body)
(*
     group (string "let" ^^ space ^^
       pat p ^^ opt_type_annotation ty ^^
       op "=" ^^ group (exp e) ^^
       string ";") ^^ break 1 ^^ exp body*)
  | Tuple (None, t) -> fields ~tcomma:true (exp ~prec:Exp) t
  | Tuple (Some Anon_tag, Ftuple []) -> parens empty
  | Tuple (Some tag, Ftuple []) -> tuple_tag tag
  | Tuple (Some Anon_tag, (Ftuple _ as t)) -> fields ~tcomma:true (exp ~prec:Exp) t
  | Tuple (Some tag, t) -> tuple_tag tag ^^ fields ~tcomma:false (exp ~prec:Exp) t
  | App (f, args) ->
     let args = List.map (function
       | (Some s, x) -> string s ^^ string ":" ^^ space ^^ exp ~prec x
       | (None, x) -> exp ~prec:Max x) args in
     exp ~prec f ^^ parens (sep comma args)
  | Proj (e, f) -> exp ~prec e ^^ char '.' ^^ field_name (Field_named (fst f))
  | If (e, t, f) ->
     string "if" ^^ blank 1 ^^ exp ~prec e ^^ block t ^^ blank 1 ^^ string "else" ^^ block f
  | Match ((e, _loc), cs) ->
     string "match" ^^
       group (indent (break 1 ^^ separate_map (comma ^^ break 1) (exp ~prec) e) ^^ break 1) ^^
       braces' (indent (break 1 ^^ ifflat empty (string "| ") ^^ cases cs) ^^ break 1)
  | Typed (e, t) -> parens (exp ~prec e ^^ opt_type_annotation (Some t))
  | Pragma s -> char '@' ^^ string s

and fndef ~name (poly, params, ty, body) =
  group (
    string "fn" ^^ space ^^
      (match name with None -> empty | Some s -> symbol s) ^^
      (match poly with
      | None -> empty
      | Some poly -> typolybounds poly) ^^
     parens (sep comma (List.map parameter params)) ^^
     (match ty with
      | None -> empty
      | Some ty ->
         indent (blank 1 ^^ group (string "->" ^^ break 1 ^^ group (tyexp ~prec:Term ty))))) ^^
    block body

and block e =
  space ^^ braces' (indent (break 1 ^^ exp ~prec:Max e) ^^ break 1)

and exp_pun = function
  | Field_named s, (Some (Var ({label=s';shift=0}, _)), _) -> s = s'
  | _ -> false
and pat_pun = function
  | Field_named s, (Some (Pbind ((s', _), (Some Pany, _))), _) -> s = s'
  | _ -> false

and argument ~pos fn arg =
  match fn, arg with
  | _ when pos -> exp ~prec:Max arg
  | Field_named s, (Some (Var ({label=s';shift=0}, _)), _) when s = s' ->
     string "~" ^^ field_name fn
  | fn, arg ->
     string "~" ^^ field_name fn ^^ colon ^^ space ^^ exp ~prec:Max arg

and parameter (p, ty) =
  pat ~prec:Term p ^^ opt_type_annotation ~prespace:false ty

and opt_type_annotation ?(prespace=true) = function
  | Some ty -> (if prespace then blank 1 else empty) ^^ string ":" ^^ nest 2 (break 1 ^^ group (tyexp ~prec:Exp ty))
  | None -> empty

and cases cs =
  cs |> separate_map (break 1 ^^ string "| ") @@ fun ((pps,_), e) ->
    (pps |> separate_map (break 1 ^^ string "| ") @@ fun ps ->
      group (separate_map (comma ^^ break 1) (pat ~prec:Term) ps))
    ^^ space ^^ string "=>" ^^ group (indent (break 1 ^^ exp ~prec:Term e))

and pat ~prec p =
  match p with
  | None, _ -> string "<err>"
  | Some p, _ ->
     let doc = pat_ p in
     if pat_precedence p > prec then parens doc else doc
and pat_ p =
  let prec = pat_precedence p in
  match p with
  | Pany -> string "_"
  | Pbind (s, (Some Pany, _)) -> symbol s
  | Pbind (s, p) -> symbol s ^^ op "@" ^^ pat ~prec:Infix p
  | Ptuple (None, ts) -> fields ~tcomma:true (pat ~prec:Term) ts
  | Ptuple (Some Anon_tag, (Ftuple _ as ts)) -> fields ~tcomma:true (pat ~prec:Term) ts
  | Ptuple (Some tag, Ftuple []) -> tuple_tag tag
  | Ptuple (Some tag, ts) -> tuple_tag tag ^^ fields ~tcomma:false (pat ~prec:Term) ts
  | Por (p, q) -> pat ~prec p ^^ op "|" ^^ pat ~prec q

and tyexp ~prec t =
  match t with
  | None, _ -> string "<err>"
  | Some t, _ ->
     let doc = tyexp_ t in
     if ty_precedence t > prec then parens doc else doc
and tyexp_ t =
  let prec = ty_precedence t in
  match t with
  | Trecord (tag, args, fs) ->
     let tag' =
       match tag, fs with
       | None, _ -> empty
       | Some Anon_tag, Ftuple _ -> empty
       | Some t, _ -> tuple_tag t
     in
     let args =
       let tyarg = function
         | None, _ -> string "<err>"
         | Some (Arg_pos t), _ -> string "+" ^^ tyexp ~prec:Exp t
         | Some (Arg_neg t), _ -> string "-" ^^ tyexp ~prec:Exp t
         | Some (Arg_gen t), _ -> tyexp ~prec:Exp t
         | Some (Arg_both {neg;pos}), _ -> string "-" ^^ tyexp ~prec:Term neg ^^ break 1 ^^ string "+" ^^ tyexp ~prec:Term pos
       in
       match args with
       | [] -> empty
       | args ->
          brackets (separate_map (comma ^^ break 1) tyarg args)
     in
     let fs =
       match tag, fs with
       | Some Anon_tag, Ftuple _ ->
          fields ~tcomma:true (tyexp ~prec:Exp) fs
       | Some _, Ftuple [] -> empty
       | Some _, _ -> fields ~tcomma:false (tyexp ~prec:Exp) fs
       | None, _ -> fields ~tcomma:true (tyexp ~prec:Exp) fs
     in
     group (tag' ^^ args) ^^ fs
  | Tfunc (args, ret) ->
     let args =
       match args with
       | [arg] -> tyexp ~prec:Term arg
       | args ->
          parens (sep comma (List.map (tyexp ~prec:Exp) args))
     in
     args ^^ space ^^ group (string "->" ^^ break 1 ^^ group (tyexp ~prec:Exp ret))
  | Tforall (bounds, body) ->
      typolybounds bounds ^^ space ^^ tyexp ~prec:Exp body
  | Ttyvar v ->
     symbol v
  | Tjoin (s, t) -> tyexp ~prec s ^^ op "|" ^^ tyexp ~prec t
  | Ttop -> string "Any"
  | Tbot -> string "Nothing"

and argtype ~pos fn ty =
  if pos then tyexp ~prec:Exp ty
  else string "~" ^^ field_name fn ^^ colon ^^ space ^^ tyexp ~prec:Exp ty

and typolybounds bs =
  let bound = function
    | (a, None) -> symbol a
    | (a, Some ty ) ->
       group (symbol a ^^ op "<:" ^^ tyexp ~prec:Max ty) in
  brackets (separate (comma ^^ break 1) (List.map bound bs))

let exp = exp ~prec:Max
let tyexp = tyexp ~prec:Max
let pat = pat ~prec:Term

let variance_spec v =
  match v.occurs_neg, v.occurs_pos with
  | `No, `No -> "0 "
  | `No, `Strict -> "+"
  | `No, `Yes -> "++"
  | `Yes, `No -> "-"
  | `Yes, `Strict -> "+-"
  | `Yes, `Yes -> "++-"

let decl_ty_param ((v, s) : Exp.variance_spec option * symbol) =
  match v with
  | None -> symbol s
  | Some v ->
     string (variance_spec v) ^^ symbol s

let decl_ty_params = function
  | [] -> empty
  | ps -> brackets (separate_map (comma ^^ break 1) decl_ty_param ps)

let decl_ty_body = function
  | Dty_record (fs,_) ->
     fields ~tcomma:false tyexp fs
  | Dty_variant vs ->
     let variant (s, (fs,_)) = symbol s ^^ fields ~tcomma:false tyexp fs in
     (* FIXME share code with Match? *)
     braces' (indent (break 1 ^^ ifflat empty (string "| ") ^^ separate_map (break 1 ^^ string "| ") variant vs) ^^ break 1)

let decl = function
  | None, _ -> string "<err>"
  | Some (Dfn (s, def)), _ ->
     fndef ~name:(Some s) def
  | Some (Dtype (s, ps, body)), _ ->
     string "type" ^^ space ^^ symbol s ^^ decl_ty_params ps ^^ decl_ty_body body


let prog p = separate hardline (List.map decl p)
