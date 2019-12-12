%token <string> SYMBOL
%token <int> INT
%token <string> STRING
%token SHIFT
%token EOF WS COMMENT NL ERROR
%token LPAR RPAR LBRACE RBRACE LBRACK RBRACK
%token COLON EQUALS DOT COMMA SEMI UNDER QUESTION ARROW AMPER VBAR
%token FN LET TRUE FALSE IF ELSE

%{ open Exp %}
%start <Exp.exp> prog
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

exp: e = mayloc(exp_) { e }
exp_:
| v = ident
  { Var v }
| k = literal
  { Lit k }
| FN; params = tuple(pat, field, field); LBRACE; body = exp; RBRACE
  { Fn (params, body) }
| fn = exp; args = tuple(exp, field, field)
  { App (fn, args) }
| t = tuple(exp, field, nfield)
  { Tuple t }
| LPAR; e = exp; RPAR
  { Parens e }
| e = exp; DOT; f = symbol
  { Proj (e, f) }
| LPAR; e = exp; COLON; t = tyexp; RPAR
  { Typed (e, t) }

tuple(X, field, field1): e = mayloc(tuple_(X, field, field1)) { e }
tuple_(X, field, field1):
(* 0-tuples: no commas *)
| LPAR; RPAR
  { [] }
(* n-tuples with at least one comma (possibly trailing) *)
| LPAR; f = field(X); fs = tuple1(X, field); RPAR
  { f :: fs }
(* 1-tuples with no comma *)
| LPAR; f = field1(X); RPAR
  { [f] }

tuple1(X, field):
| COMMA; { [] }
| COMMA; f = field(X) { [f] }
| COMMA; f = field(X); fs = tuple1(X, field)  { f :: fs }

%inline field(X):
| e = pfield(X) { e }
| e = nfield(X) { e }
pfield(X):
| e = X
  { Fpositional (None, e) }
| e = X; COLON; ty = tyexp
  { Fpositional (Some ty, e) }
nfield(X):
| DOT; f = symbol; EQUALS; e = X
  { Fnamed(f, None, Some e) }
| DOT; f = symbol
  { Fnamed(f, None, None) }
| DOT; f = symbol; COLON; ty = tyexp; EQUALS; e = X
  { Fnamed(f, Some ty, Some e) }
| DOT; f = symbol; COLON; ty = tyexp
  { Fnamed(f, Some ty, None) }

pat: p = mayloc(pat_) { p }
pat_:
| v = symbol
  { Pvar v }
| t = tuple(pat, field, nfield)
  { Ptuple t }
| LPAR; t = pat; RPAR
  { Pparens t }

tyexp: t = mayloc(tyexp_) { t }
tyexp_:
| t = ident
  { Tnamed t }
| t = tuple(tyexp, tyexp_field, tyexp_nfield)
  { Trecord(t, `Closed) }
| t = tuple(tyexp, tyexp_field, tyexp_field); ARROW; r = tyexp
  { Tfunc (t, r) }
| LPAR; t = tyexp; RPAR
  { Tparen (t) }
| t1 = tyexp; VBAR; t2 = tyexp
  { Tjoin(t1, t2) }
| t1 = tyexp; AMPER; t2 = tyexp
  { Tmeet(t1, t2) }

%inline tyexp_field(X):
| e = X
  { TFpositional e }
| e = tyexp_nfield(X)
  { e }
tyexp_nfield(X):
| DOT; f = symbol; COLON; e = X
  { TFnamed (f, e) }
