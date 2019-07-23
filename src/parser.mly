%token <string> IDENT
%token <int> INT
%token <string> STRING
%token EOF WS COMMENT NL ERROR
%token LPAR RPAR LBRACE RBRACE LBRACK RBRACK
%token COLON EQUALS DOT COMMA SEMI UNDER QUESTION
%token FN LET TRUE FALSE IF ELSE

%{ open Exp %}
%start <Exp.exp> prog
%%

%inline loc(X): e = X
  { e, { source = "FIXME"; loc_start = $startpos(e); loc_end = $endpos(e) } }
%inline mayfail(X): e = X { Some e } (* | error { None } *) 
%inline mayloc(X): e = loc(mayfail(X)) { e }

prog: e = exp; EOF { e }

symbol: s = loc(IDENT) { s } 

literal: l = loc(literal_) { l }
literal_:
| n = INT
  { Int n }
| s = STRING
  { String s }

exp: e = mayloc(exp_) { e }
exp_:
| v = symbol
  { Var v }
| k = literal
  { Lit k }
| FN; params = tuple(pat, field); LBRACE; body = exp; RBRACE
  { Fn (params, body) }
| fn = exp; args = tuple(exp, field)
  { App (fn, args) }
| t = tuple(exp, nfield)
  { Tuple t }
| LPAR; e = exp; RPAR
  { Parens e }
| e = exp; DOT; f = loc(IDENT)
  { Proj (e, f) }

tuple(X, field1): e = mayloc(tuple_(X, field1)) { e }
tuple_(X, field1):
(* 0-tuples: no commas *)
| LPAR; RPAR
  { [] }
(* n-tuples with at least one comma (possibly trailing) *)
| LPAR; f = field(X); fs = tuple1(X); RPAR
  { f :: fs }
(* 1-tuples with no comma *)
| LPAR; f = field1(X); RPAR
  { [f] }

tuple1(X):
| COMMA; { [] }
| COMMA; f = field(X) { [f] }
| COMMA; f = field(X); fs = tuple1(X)  { f :: fs }

%inline field(X):
| e = pfield(X) { e }
| e = nfield(X) { e }
pfield(X):
| e = X
  { { f_name = Fpositional; f_type = None; f_defn = Some e } }
| e = X; COLON; ty = tyexp
  { { f_name = Fpositional; f_type = Some ty; f_defn = Some e } }
nfield(X):
| DOT; f = symbol; EQUALS; e = X
  { { f_name = Fnamed f; f_type = None; f_defn = Some e } }

pat: p = mayloc(pat_) { p }
pat_:
| v = symbol
  { Pvar v }
| t = tuple(pat, nfield)
  { Ptuple t }
| LPAR; t = pat; RPAR
  { Pparens t }

tyexp: t = mayloc(tyexp_) { t }
tyexp_:
| t = symbol
  { Tnamed t }
