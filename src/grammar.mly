%token <string> SYMBOL
%token <int> INT
%token <string> STRING
%token <string> PRAGMA
%token SHIFT
%token EOF WS COMMENT NL ERROR
%token LPAR RPAR LBRACE RBRACE LBRACK RBRACK
%token COLON EQUALS DOT DOTS COMMA SEMI UNDER QUESTION ARROW AMPER VBAR
%token FN LET TRUE FALSE IF ELSE AS TILDE
%token SUBTYPE SUPTYPE

%nonassoc ARROW
%left VBAR
%right AS
%right SEMI

%{ open Tuple_fields open Exp %}
%start <[`Exp of Exp.exp | `Sub of Exp.tyexp * Exp.tyexp]> prog

%{
let parse_fields fs = collect_fields fs
let parse_tyfields fs = collect_fields fs
%}
%%


%inline id(X): X { $1 }
%inline loc(X): e = X
  { e, { source = "FIXME"; loc_start = $startpos(e); loc_end = $endpos(e) } }
%inline mayfail(X): e = X { Some e } | ERROR { None }
%inline mayloc(X): e = loc(mayfail(X)) { e }

prog:
| e = exp; EOF { `Exp e }
| COLON; t1 = tyexp; SUBTYPE; t2 = tyexp; EOF { `Sub (t1, t2) }

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
| FN;
  poly = ioption(typolybounds);
  LPAR; params = separated_list(COMMA, parameter); RPAR;
  ty = ioption(ARROW; t = tyexp {t});
  LBRACE; body = exp; RBRACE
  { Fn (poly, parse_fields params, ty, body) }
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
| t = term_
  { t }

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

| LPAR; RPAR
  { Tuple (parse_fields []) }
| LPAR; e = exp; RPAR
  { Parens e }
| LPAR; e = exp; COLON; t = tyexp; RPAR
  { Typed (e, t) }
| LPAR; e = exp; COMMA; es = separated_list(COMMA, exp); RPAR
  { Tuple (parse_fields (List.map (fun e -> Fpos e) (e :: es))) }
| LBRACE; es = separated_nonempty_list(COMMA, named_field); RBRACE
  { Tuple (parse_fields es) }

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
| v = symbol
  { Pvar v }
| LPAR; RPAR
  { Ptuple (parse_fields []) }
| LPAR; DOTS; RPAR
  { Ptuple (parse_fields [Fdots]) }
| LPAR; p = pat; RPAR
  { Pparens p }
| LPAR; p = pat; COMMA; ps = separated_list(COMMA, pat_or_dots); RPAR
  { Ptuple (parse_fields (Fpos p :: ps)) }
| LBRACE; ps = separated_nonempty_list(COMMA, named_field_pat); RBRACE
  { Ptuple (parse_fields ps) }

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
| t = ident
  { Tnamed t }
| LPAR; t = tyfields; RPAR
  { match t with
    | [Fpos t] -> Tparen t
    | fs -> Trecord (parse_tyfields fs) }
| LBRACE; ts = separated_nonempty_list(COMMA, named_field_typ); RBRACE
  { Trecord (parse_tyfields ts) }
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
| s = symbol; SUBTYPE;  b = tyexp
  { s, Some b }
| s = symbol { s, None }
