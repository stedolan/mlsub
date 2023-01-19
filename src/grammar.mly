%token <string> SYMBOL
%token <string> USYMBOL
%token <string> QUSYMBOL
%token <int> INT
%token <string> STRING
%token <string> PRAGMA
%token SHIFT
%token EOF WS COMMENT NL ERROR
%token LPAR RPAR LBRACE RBRACE LBRACK RBRACK
%token COLON EQUALS DOT DOTS COMMA SEMI UNDER QUESTION ARROW FATARROW AMPER VBAR
%token FN LET TRUE FALSE IF ELSE AS TILDE
%token SUBTYPE SUPTYPE
%token MATCH

%nonassoc low_priority
%nonassoc ARROW
%nonassoc LPAR LBRACE
%left VBAR
%right AS
%right SEMI
(*%nonassoc high_priority*)

%{ open Tuple_fields open Exp open Location %}
%start <[`Exp of Exp.exp | `Sub of Exp.tyexp * Exp.tyexp]> prog

%{
let parse_fields fs = collect_fields fs
let parse_tyfields fs = collect_fields fs
%}
%%


%inline id(X): X { $1 }
%inline loc(X): e = X
  { e, [{ loc_start = $startpos(e); loc_end = $endpos(e) }] }
%inline mayfail(X): e = X { Some e } | ERROR { None }
%inline mayloc(X): e = loc(mayfail(X)) { e }

prog:
| e = exp; EOF { `Exp e }
| COLON; t1 = tyexp; SUBTYPE; t2 = tyexp; EOF { `Sub (t1, t2) }

symbol: s = loc(SYMBOL) { s }
usymbol: s = loc(USYMBOL) { s }
qusymbol: s = loc(QUSYMBOL) { s }

(* FIXME: probably a bad idea. Enforce case conventions *)
anysymbol:
| s = symbol { s }
| s = usymbol { s }

ident: v = loc(ident_) { v }
ident_:
| s = SYMBOL
  { { label = s; shift = 0 } }
| v = ident_; SHIFT
  { { v with shift = v.shift + 1 } }

(* FIXME: remove and enforce case conventions *)
anyident: v = loc(anyident_) { v }
anyident_:
| s = SYMBOL
  { { label = s; shift = 0 } }
| s = USYMBOL
  { { label = s; shift = 0 } }
| v = anyident_; SHIFT
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
| FN; def = fndef
  { Fn def }
| FN; s = symbol; def = fndef; e = exp %prec SEMI
  { FnDef (s, def, e) }
| IF; e = exp; LBRACE; t = exp; RBRACE; ELSE; LBRACE; f = exp; RBRACE
  { If (e, t, f) }
| s = PRAGMA
  { Pragma s }
| LET; p = pat; EQUALS; e = exp; SEMI; body = exp
  { Let (p, None, e, body) }
| LET; p = pat; COLON; t = tyexp; EQUALS; e = exp; SEMI; body = exp
  { Let (p, Some t, e, body) }
| e1 = exp; SEMI; e2 = exp
  { Seq (e1, e2) }
| MATCH; es = separated_nonempty_list(COMMA, exp); LBRACE; cs = cases; RBRACE
  { Match (es, cs) }
| t = term_
  { t }

fndef:
| poly = ioption(typolybounds);
  LPAR; params = separated_list(COMMA, parameter); RPAR;
  ty = ioption(ARROW; t = tyexp {t});
  LBRACE; body = exp; RBRACE
  { (poly, parse_fields params, ty, body) }

term: e = mayloc(term_) { e }
term_:
| v = ident
  { Var v }
| k = literal
  { Lit k }
| fn = term; LPAR; args = separated_list(COMMA, argument); RPAR
  { App (fn, parse_fields args) }
| e = term; DOT; f = symbol
  { Proj (e, f) }

| tag = usymbol %prec low_priority
  { Tuple (Some tag, parse_fields []) }
| tag = ioption(usymbol); LPAR; RPAR
  { Tuple (tag, parse_fields []) }
| LPAR; e = exp; RPAR
  { Parens e }
| LPAR; e = exp; COLON; t = tyexp; RPAR
  { Typed (e, t) }
| tag = usymbol; LPAR; e = exp; RPAR
  { Tuple(Some tag, parse_fields [Fpos e]) }
| tag = ioption(usymbol); LPAR; e = exp; COMMA; es = separated_list(COMMA, exp); RPAR
  { Tuple (tag, parse_fields (List.map (fun e -> Fpos e) (e :: es))) }
| tag = ioption(usymbol); LBRACE; es = separated_nonempty_list(COMMA, named_field); RBRACE
  { Tuple (tag, parse_fields es) }

named_field:
| f = SYMBOL; COLON; e = exp
  { Fnamed (f, e) }
| f = ident
  { Fnamed ((fst f).label, (Some (Var f), snd f)) }

argument:
| e = exp
  { Fpos e }
| TILDE; f = ident
  { Fnamed ((fst f).label, (Some (Var f), snd f)) }
| TILDE; f = SYMBOL; COLON; e = exp
  { Fnamed (f, e) }

parameter:
| p = pat; ty = opt_type_annotation
  { Fpos (p, ty) }
| TILDE; f = symbol; ty = opt_type_annotation
  { Fnamed (fst f, ((Some (Pvar f), snd f), ty)) }
| TILDE; f = SYMBOL; p = pat; ty = opt_type_annotation
  { Fnamed (f, (p, ty)) }

opt_type_annotation:
| 
  { None }
| COLON; ty = tyexp
  { Some ty }

cases:
| { [] }
| ioption(VBAR); cs = separated_nonempty_list(VBAR, case) { cs }

case:
| ps = separated_nonempty_list(VBAR, separated_nonempty_list(COMMA, onepat)); FATARROW; e = exp { ps, e }

tyfield:
| t = tyexp
  { Fpos t }
| TILDE; f = SYMBOL; COLON; e = tyexp
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
| p = onepat_
  { p }
| p = onepat; VBAR; q = pat
  { Por(p, q) }

onepat: p = mayloc(onepat_) { p }
onepat_:
| v = symbol
  { Pvar v }
| UNDER
  { Pany }
| tag = usymbol
  { Ptuple (Some tag, parse_fields []) }
| tag = ioption(usymbol); LPAR; RPAR
  { Ptuple (tag, parse_fields []) }
| tag = ioption(usymbol); LPAR; DOTS; RPAR
  { Ptuple (tag, parse_fields [Fdots]) }
| LPAR; p = pat; RPAR
  { Pparens p }
| tag = usymbol; LPAR; p = pat; RPAR
  { Ptuple (Some tag, parse_fields [Fpos p]) }
| tag = ioption(usymbol); LPAR; p = pat; COMMA; ps = separated_list(COMMA, pat_or_dots); RPAR
  { Ptuple (tag, parse_fields (Fpos p :: ps)) }
| tag = ioption(usymbol); LBRACE; ps = separated_nonempty_list(COMMA, named_field_pat); RBRACE
  { Ptuple (tag, parse_fields ps) }

pat_or_dots:
| p = pat
  { Fpos p }
| DOTS
  { Fdots }

named_field_pat:
| f = SYMBOL; COLON; p = pat
  { Fnamed(f, p) }
| f = symbol
  { Fnamed(fst f, (Some (Pvar f), snd f)) }
| DOTS
  { Fdots }

typolybounds:
| LBRACK; t = separated_list(COMMA, typolybound); RBRACK
  { t }

tyexp: t = mayloc(tyexp_) { t }
tyexp_:
| t = anyident
  { Tnamed t }
| tag = qusymbol %prec low_priority
  { Trecord(Some tag, parse_tyfields []) }
| tag = ioption(qusymbol); LPAR; t = tyfields; RPAR
  { match tag, t with
    | None, [Fpos t] -> Tparen t
    | tag, fs -> Trecord (tag, parse_tyfields fs) }
| tag = ioption(qusymbol);
  LBRACE; ts = separated_nonempty_list(COMMA, named_field_typ); RBRACE

  { Trecord (tag, parse_tyfields ts) }
(* FIXME: what does (...) -> a | b mean? (prec of -> and |) *)
| LPAR; t = tyfields; RPAR; ARROW; r = tyexp
  { Tfunc (parse_tyfields t, r) }
| t1 = tyexp; VBAR; t2 = tyexp
  { Tjoin(t1, t2) }
| t = typolybounds; b = tyexp %prec AS (* kinda hack *)
  { Tforall(t, b) }

named_field_typ:
| f = SYMBOL; COLON; t = tyexp
  { Fnamed(f, t) }
| DOTS
  { Fdots }

typolybound:
| s = anysymbol; SUBTYPE; b = tyexp
  { s, Some b }
| s = anysymbol { s, None }
