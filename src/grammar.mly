%token <string> SYMBOL
%token <int> INT
%token <string> STRING
%token <string> PRAGMA
%token SHIFT
%token EOF WS COMMENT NL ERROR
%token LPAR RPAR LBRACE RBRACE LBRACK RBRACK
%token COLON EQUALS DOT DOTS COMMA SEMI UNDER QUESTION ARROW AMPER VBAR
%token FN LET TRUE FALSE IF ELSE

%nonassoc ARROW
%left AMPER
%left VBAR

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
| TRUE
  { Bool true }
| FALSE
  { Bool false }

exp: e = mayloc(exp_) { e }
exp_:
| v = ident
  { Var v }
| k = literal
  { Lit k }
| FN; params = etuple(pat); LBRACE; body = exp; RBRACE
  { Fn (fst params, body) }
| fn = exp; args = etuple(exp)
  { App (fn, fst args) }
| t = etuple(exp)
  { match t with
    | (t, None) -> Tuple t
    | (_, Some (e, None)) -> Parens e
    | (_, Some (e, Some ty)) -> Typed (e, ty) }
| e = exp; DOT; f = symbol
  { Proj (e, f) }
| IF; e = exp; LBRACE; t = exp; RBRACE; ELSE; LBRACE; f = exp; RBRACE
  { If (e, t, f) }
| s = PRAGMA
  { Pragma s }

%inline separated_opt_pair(X, sep, Y):
| x = X { Some x, None }
| y = Y { None, Some y }
| x = X; sep; y = Y { Some x, Some y }

tuple(X, pfield, nfield):
| LPAR; t = tuple_positional(X, pfield, nfield)
  { let (p,n,(e,t)) = t in (p,n,e,t) }
| LPAR; t = tuple_named(X, pfield, nfield)
  { let (n,(e,t)) = t in ([], n, e, t) }
| LPAR; t = tuple_end
  { let (e, t) = t in ([], [], e, t) }
tuple_positional(X, pfield, nfield):
| p = pfield(X); COMMA; xs = tuple_positional(X, pfield, nfield)
  { let (ps,n,e) = xs in (p::ps,n,e) }
| p = pfield(X); COMMA; xs = tuple_named(X,pfield,nfield)
  { let (n,e) = xs in ([p],n,e) }
| p = pfield(X); e = tuple_end
  { [p], [], e }
tuple_named(X,pfield,nfield):
| n = nfield(X); COMMA; xs = tuple_named(X, pfield, nfield)
  { let (ns, e) = xs in (n::ns, e) }
| n = nfield(X); e = tuple_end
  { [n], e }
tuple_end:
| RPAR { `Closed, false }
| COMMA; RPAR { `Closed, true }
| COMMA; DOTS; RPAR { `Open, true }

etuple(X): e = tuple(X, pos_field, named_field)
{
  let fields_pos, fields_named, fields_open, trail = e in
  let fields = { fields_pos; fields_named; fields_open } in
  let parens =
    match fields with
    | { fields_pos = [e]; fields_named = []; fields_open = `Closed }
       when not trail -> Some e
    | _ -> None in
  fields, parens
}

pos_field(X):
| e = X
  { (e, None) }
| e = X; COLON; ty = tyexp
  { (e, Some ty) }

named_field(X):
| DOT; f = symbol; EQUALS; e = X
  { (f, Some e, None) }
| DOT; f = symbol
  { (f, None, None) }
| DOT; f = symbol; COLON; ty = tyexp; EQUALS; e = X
  { (f, Some e, Some ty) }
| DOT; f = symbol; COLON; ty = tyexp
  { (f, None, Some ty) }

tytuple: e = tuple(tyexp, ty_pos_field, ty_named_field)
{
  let tyfields_pos, tyfields_named, tyfields_open, trail = e in
  let fields = { tyfields_pos; tyfields_named; tyfields_open } in
  let parens =
    match fields with
    | { tyfields_pos = [e]; tyfields_named = []; tyfields_open = `Closed}
      when not trail -> Some e
    | _ -> None in
  fields, parens
}

ty_pos_field(X): e = X { e }
ty_named_field(X): DOT; f = symbol; COLON; e = X { f, e }

pat: p = mayloc(pat_) { p }
pat_:
| v = symbol
  { Pvar v }
| t = etuple(pat)
  { match t with
    | t, None -> Ptuple t
    | _, Some (t, None) -> Pparens t
    | _, Some (_t, _ty) -> failwith "unimplemented" (* Ptyped? *) }

tyexp: t = mayloc(tyexp_) { t }
tyexp_:
| t = ident
  { Tnamed t }
| t = tytuple
  { match t with fs, None -> Trecord fs | _, Some t -> Tparen t }

(* FIXME: what does (...) -> a | b mean? (prec of -> and |) *)
| t = tytuple; ARROW; r = tyexp
  { Tfunc (fst t, r) }
| t1 = tyexp; VBAR; t2 = tyexp
  { Tjoin(t1, t2) }
| t1 = tyexp; AMPER; t2 = tyexp
  { Tmeet(t1, t2) }
