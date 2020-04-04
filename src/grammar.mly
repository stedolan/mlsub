%token <string> SYMBOL
%token <int> INT
%token <string> STRING
%token <string> PRAGMA
%token SHIFT
%token EOF WS COMMENT NL ERROR
%token LPAR RPAR LBRACE RBRACE LBRACK RBRACK
%token COLON EQUALS DOT DOTS COMMA SEMI UNDER QUESTION ARROW AMPER VBAR
%token FN LET TRUE FALSE IF ELSE AS

%nonassoc ARROW
%left AMPER
%left VBAR

%{ open Exp %}
%start <Exp.exp> prog

%{
type ('pos, 'named) field =
  | Fpos of 'pos
  | Fnamed of 'named
  | Fdots
  | Fempty

let rec collect_fields pos named = function
  | [] | [Fempty] -> List.rev pos, List.rev named, `Closed
  | Fempty :: _ -> assert false
  | [Fdots] -> List.rev pos, List.rev named, `Open
  | Fdots :: _ ->
     failwith "'...' can only appear at end of tuple"
  | Fpos _ :: _ when named <> [] ->
     failwith "positional items must precede named ones"
  | Fpos p :: fs ->
     collect_fields (p :: pos) named fs
  | Fnamed n :: fs ->
     collect_fields pos (n :: named) fs

let parse_fields fs =
  let (fields_pos, fields_named, fields_open) =
    collect_fields [] [] fs in
  { fields_pos; fields_named; fields_open }

let parse_tyfields fs =
  let (tyfields_pos, tyfields_named, tyfields_open) =
    collect_fields [] [] fs in
  { tyfields_pos; tyfields_named; tyfields_open }

%}
%%

%inline loc(X): e = X
  { e, { source = "FIXME"; loc_start = $startpos(e); loc_end = $endpos(e) } }
%inline mayfail(X): e = X { Some e } (* | error { None } *) 
%inline mayloc(X): e = loc(mayfail(X)) { e }

prog: e = exp; EOF { e }

symbol: s = loc(SYMBOL) { s } 
ident: v = loc(ident_) { v }
ident_:
| s = SYMBOL
  { { label = s; shift = 0 } }
| v = ident_; SHIFT
  { { v with shift = v.shift + 1 } }

literal: l = loc(literal_) { l }
literal_:
| n = INT
  { Int n }
| s = STRING
  { String s }
| TRUE
  { Bool true }
| FALSE
  { Bool false }

exp: e = mayloc(exp_) { e }
exp_:
| FN; LPAR; params = fields(pat, AS); RPAR; LBRACE; body = exp; RBRACE
  { Fn (parse_fields params, body) }
| IF; e = exp; LBRACE; t = exp; RBRACE; ELSE; LBRACE; f = exp; RBRACE
  { If (e, t, f) }
| s = PRAGMA
  { Pragma s }
| LET; p = fields(pat, AS); EQUALS; e = fields(exp, EQUALS); SEMI; body = exp
  { Let (parse_fields p, parse_fields e, body) }
| t = term_
  { t }

term: e = mayloc(term_) { e }
term_:
| v = ident
  { Var v }
| k = literal
  { Lit k }
| fn = term; LPAR; args = fields(exp, EQUALS); RPAR
  { App (fn, parse_fields args) }
| e = term; DOT; f = symbol
  { Proj (e, f) }
| LPAR; t = fields(exp, EQUALS); RPAR
  { match t with
    | [Fpos (e, None)] -> Parens e
    | [Fpos (e, Some ty)] -> Typed (e, ty)
    | fs -> Tuple (parse_fields fs) }

field(defn, named_sep):
| e = defn
  { Fpos (e, None) }
| e = defn; COLON; ty = tyexp
  { Fpos (e, Some ty) }
| DOT; f = symbol
  { Fnamed (f, None, None) }
| DOT; f = symbol; named_sep; e = defn
  { Fnamed (f, Some e, None) }
| DOT; f = symbol; COLON; ty = tyexp; named_sep; e = defn
  { Fnamed (f, Some e, Some ty) }
| DOT; f = symbol; COLON; ty = tyexp
  { Fnamed (f, None, Some ty) }
| DOTS
  { Fdots }

fields(defn, named_sep):
|
  { [Fempty] }
| f = field(defn, named_sep)
  { [f] }
| f = field(defn, named_sep); COMMA; fs = fields(defn, named_sep)
  { f :: fs }

tyfield:
| t = tyexp
  { Fpos t }
| DOT; f = symbol; COLON; e = tyexp
  { Fnamed (f, e) }
| DOTS
  { Fdots }

tyfields:
|
  { [Fempty] }
| f = tyfield
  { [f] }
| f = tyfield; COMMA; fs = tyfields
  { f :: fs }

pat: p = mayloc(pat_) { p }
pat_:
| v = symbol
  { Pvar v }
| LPAR; t = fields(pat, AS); RPAR
  { match t with
    | [Fpos (p, None)] -> Pparens p
    | [Fpos (p, Some ty)] -> Ptyped (p, ty)
    | p -> Ptuple (parse_fields p) }

tyexp: t = mayloc(tyexp_) { t }
tyexp_:
| t = ident
  { Tnamed t }
| LPAR; t = tyfields; RPAR
  { match t with
    | [Fpos t] -> Tparen t
    | fs -> Trecord (parse_tyfields fs) }
(* FIXME: what does (...) -> a | b mean? (prec of -> and |) *)
| LPAR; t = tyfields; RPAR; ARROW; r = tyexp
  { Tfunc (parse_tyfields t, r) }
| t1 = tyexp; VBAR; t2 = tyexp
  { Tjoin(t1, t2) }
| t1 = tyexp; AMPER; t2 = tyexp
  { Tmeet(t1, t2) }
