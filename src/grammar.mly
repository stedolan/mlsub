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
%left AMPER
%left VBAR
%right AS 


%{ open Tuple_fields open Exp %}
%start <[`Exp of Exp.exp | `Sub of Exp.tyexp * Exp.tyexp]> prog

%{
let parse_fields fs = collect_fields fs
let parse_tyfields fs = collect_fields fs
%}
%%

%inline loc(X): e = X
  { e, { source = "FIXME"; loc_start = $startpos(e); loc_end = $endpos(e) } }
%inline mayfail(X): e = X { Some e } (* | error { None } *) 
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
| FN; LPAR; params = typed_fields(pat, AS); RPAR; LBRACE; body = exp; RBRACE
  { Fn (parse_fields params, None, body) }
| FN; LPAR; params = typed_fields(pat, AS); RPAR; COLON; ty = tyexp; LBRACE; body = exp; RBRACE
  { Fn (parse_fields params, Some ty, body) }
| IF; e = exp; LBRACE; t = exp; RBRACE; ELSE; LBRACE; f = exp; RBRACE
  { If (e, t, f) }
| s = PRAGMA
  { Pragma s }
| LET; p = pat; EQUALS; e = exp; SEMI; body = exp
  { Let (p, None, e, body) }
| LET; p = pat; COLON; t = tyexp; EQUALS; e = exp; SEMI; body = exp
  { Let (p, Some t, e, body) }
| t = term_
  { t }

term: e = mayloc(term_) { e }
term_:
| v = ident
  { Var v }
| k = literal
  { Lit k }
| fn = term; LPAR; args = untyped_fields(exp, EQUALS); RPAR
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
  { Tuple (parse_fields (List.map (fun e -> Fpos (Some e, None)) (e :: es))) }
| LBRACE; es = separated_nonempty_list(COMMA, named_field); RBRACE
  { Tuple (parse_fields es) }

named_field:
| f = SYMBOL; COLON; e = exp
  { Fnamed (f, (Some e, None)) }
| f = SYMBOL
  { Fnamed (f, (None, None)) }

typed_field(defn, named_sep):
| e = defn
  { Fpos (Some e, None) }
| e = defn; COLON; ty = tyexp
  { Fpos (Some e, Some ty) }
| DOT; f = SYMBOL
  { Fnamed (f, (None, None)) }
| DOT; f = SYMBOL; named_sep; e = defn
  { Fnamed (f, (Some e, None)) }
| DOT; f = SYMBOL; COLON; ty = tyexp; named_sep; e = defn
  { Fnamed (f, (Some e, Some ty)) }
| DOT; f = SYMBOL; COLON; ty = tyexp
  { Fnamed (f, (None, Some ty)) }
| DOTS
  { Fdots }

typed_fields(defn, named_sep):
|
  { [Fempty] }
| f = typed_field(defn, named_sep)
  { [f] }
| f = typed_field(defn, named_sep); COMMA; fs = typed_fields(defn, named_sep)
  { f :: fs }


untyped_field(defn, named_sep):
| e = defn
  { Fpos (Some e) }
| DOT; f = SYMBOL
  { Fnamed (f, None) }
| DOT; f = SYMBOL; named_sep; e = defn
  { Fnamed (f, Some e) }
| DOTS
  { Fdots }

untyped_fields(defn, named_sep):
|
  { [Fempty] }
| f = untyped_field(defn, named_sep)
  { [f] }
| f = untyped_field(defn, named_sep); COMMA; fs = untyped_fields(defn, named_sep)
  { f :: fs }


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
  { Ptuple (parse_fields ((Fpos (Some p)) :: ps)) }
| LBRACE; ps = separated_nonempty_list(COMMA, named_field_pat); RBRACE
  { Ptuple (parse_fields ps) }

pat_or_dots:
| p = pat
  { Fpos (Some p) }
| DOTS
  { Fdots }

named_field_pat:
| f = SYMBOL; COLON; p = pat
  { Fnamed(f, Some p) }
| f = SYMBOL
  { Fnamed(f, None) }
| DOTS
  { Fdots }

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
| t1 = tyexp; AMPER; t2 = tyexp
  { Tmeet(t1, t2) }
| LBRACK; t = separated_list(COMMA, typolybound); RBRACK; b = tyexp %prec AS (* kinda hack *)
  { Tforall(t, b) }

named_field_typ:
| f = SYMBOL; COLON; t = tyexp
  { Fnamed(f, t) }
| DOTS
  { Fdots }

subtype_symbol:
| SUBTYPE { `Sub }
| SUPTYPE { `Sup }

typolybound:
| s = symbol; t = subtype_symbol; b = tyexp { s, Some (t, b) }
| s = symbol { s, None }
