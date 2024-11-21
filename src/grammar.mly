%token <string> SYMBOL
%token <string> USYMBOL
%token ZERO
%token <int> NZINT
%token <string> STRING
%token <string> PRAGMA
%token SHIFT
%token EOF WS COMMENT NL ERROR
%token LPAR RPAR LBRACE RBRACE LBRACK RBRACK
%token COLON EQUALS DOT DOTS COMMA SEMI UNDER QUESTION ARROW FATARROW AMPER VBAR
%token FN LET TRUE FALSE IF ELSE TILDE HASH PLUS MINUS
%token SUBTYPE SUPTYPE AT TYPE
%token MATCH
%token T_ANY T_NOTHING
%token ABSENT

%nonassoc low_priority
%nonassoc ARROW
%nonassoc LPAR LBRACE
%left VBAR                      (* FIXME VBAR vs AT precedence? *)
%right SEMI
(*%nonassoc high_priority*)

%{ open Tuple_fields open Exp open Location %}
%start <[`Exp of Exp.exp | `Sub of Exp.tyexp * Exp.tyexp | `Prog of Exp.decl list]> prog

%{
let pvar s = Pbind (s, (Some Pany, snd s))
%}
%%


%inline id(X): X { $1 }
%inline loc(X): e = X
  { e, [{ loc_start = $startpos(e); loc_end = $endpos(e) }] }
%inline mayfail(X): e = X { Some e } | ERROR { None }
%inline mayloc(X): e = loc(mayfail(X)) { e }
%inline mayfail_opt(X): e = X { e } | ERROR { None }
%inline mayloc_opt(X): e = loc(mayfail_opt(X)) { e }

INT: ZERO { 0 } | n = NZINT { n }

prog:
| e = exp; EOF
  { `Exp e }
| LBRACE; ds = nonempty_list(decl); RBRACE; EOF
  { `Prog ds }
| COLON; t1 = tyexp; SUBTYPE; t2 = tyexp; EOF
  { `Sub (t1, t2) }

symbol: s = loc(SYMBOL) { s }
usymbol: s = loc(USYMBOL) { s }

struct_tag:
| HASH { Anon_tag }
| s = loc(HASH; s=USYMBOL {s}) { Struct_tag s }
| s = loc(USYMBOL) { Named_tag s }

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

field_name:
| f = SYMBOL
  { Field_named f }
| f = INT
  { Field_positional f }

fields_paren_items1(X):
| f = X; ioption(COMMA)
  { [f] }
| f = X; COMMA; fs = fields_paren_items1(X)
  { (f::fs) }

fields_paren_items(X):
|
  { [], false }
| f = X; c = ioption(COMMA)
  { [f], Option.is_some c }
| f = X; COMMA; fs = fields_paren_items1(X)
  { (f::fs), false }

fields_brace_item(X):
| f = loc(field_name); COLON; e = X
  { f, Mandatory (Some e) }
| f = loc(field_name); QUESTION; COLON; e = X
  { f, Optional (Some e) }
| f = loc(field_name)
  { f, Mandatory None }
| f = loc(field_name); QUESTION
  { f, Optional None }
| f = loc(field_name); QUESTION; COLON; ABSENT
  { f, Absent }
| f = loc(field_name); COLON; ABSENT
  { f, Abs_broken }

fields_brace_items1(X):
| f = fields_brace_item(X); ioption(COMMA)
  { [f] }
| f = fields_brace_item(X); ioption(COMMA); fs = fields_brace_items1(X)
  { (f::fs) }

fields_brace_items(X):
| 
  { [] }
| fs = fields_brace_items1(X)
  { fs }

%inline fields_parens(X):
| LPAR; xs = fields_paren_items(X); RPAR
  { match xs with
    | [x] as xs, false -> Some x, Ftuple xs
    | xs, _ -> None, Ftuple xs }

%inline fields_braces(X):
| LBRACE; xs = fields_brace_items(X); RBRACE
  { Frecord xs }

fields(X):
| fs = fields_parens(X) { fs }
| fs = fields_braces(X) { None, fs }

exp: e = mayloc_opt(exp_) { e }
exp_:
| FN; def = fndef
  { Some (Fn def) }
| FN; s = symbol; def = fndef; e = exp %prec SEMI
  { Some (FnDef (s, def, e)) }
| IF; e = exp; LBRACE; t = exp; RBRACE; ELSE; LBRACE; f = exp; RBRACE
  { Some (If (e, t, f)) }
| s = PRAGMA
  { Some (Pragma s) }
| LET; p = pat; EQUALS; e = exp; SEMI; body = exp
  { Some (Let (p, None, e, body)) }
| LET; p = pat; COLON; t = tyexp; EQUALS; e = exp; SEMI; body = exp
  { Some (Let (p, Some t, e, body)) }
| e1 = exp; SEMI; e2 = exp
  { Some (Seq (e1, e2)) }
| MATCH; es = loc(separated_nonempty_list(COMMA, exp)); LBRACE; cs = cases; RBRACE
  { Some (Match (es, cs)) }
| t = term_
  { t }

fndef:
| poly = ioption(typolybounds);
  LPAR; params = separated_list(COMMA, parameter); RPAR;
  ty = ioption(ARROW; t = tyterm {t});
  LBRACE; body = exp; RBRACE
  { (poly, params, ty, body) }

term: e = mayloc_opt(term_) { e }
term_:
| v = ident
  { Some (Var v) }
| k = literal
  { Some (Lit k) }
| fn = term; LPAR; args = separated_list(COMMA, argument); RPAR
  { Some (App (fn, args)) }
| e = term; DOT; f = symbol
  { Some (Proj (e, f)) }
| tag = struct_tag %prec low_priority
  { Some (Tuple (Some tag, empty_fields)) }
| LPAR; e = exp; COLON; t = tyexp; RPAR
  { Some (Typed (e, t)) }
| tag = ioption(struct_tag); fs = fields(exp)
  { match tag, fs with
    | None, (Some (Some e, _), _) -> Some e
    | None, (Some (None, _), _) -> None
    | None, (_, (Ftuple _ as fs)) -> Some (Tuple (Some Anon_tag, fs))
    | tag, (_, fs) -> Some (Tuple (tag, fs)) }

argument:
| e = exp
  { None, e }
| s=SYMBOL; COLON; e = exp
  { Some s, e }

parameter:
| p = pat; ty = opt_type_annotation { p, ty }

opt_type_annotation:
| 
  { None }
| COLON; ty = tyexp
  { Some ty }

cases:
| { [] }
| ioption(VBAR); cs = separated_nonempty_list(VBAR, case) { cs }

case:
| ps = loc(separated_nonempty_list(VBAR, separated_nonempty_list(COMMA, onepat)));
  FATARROW; e = exp
  { ps, e }

pat: p = mayloc(pat_) { p }
pat_:
| p = onepat_
  { p }
| v = symbol; AT; p = pat
  { Pbind (v, p) }
| p = onepat; VBAR; q = pat
  { Por(p, q) }

onepat: p = mayloc(onepat_) { p }
onepat_:
| v = symbol
  { pvar v }
| UNDER
  { Pany }
| HASH; tag = usymbol (* FIXME named tags *)
  { Ptuple (Some (Struct_tag tag), empty_fields) }
| tag = ioption(struct_tag); fs = fields(pat) (* FIXME named tags *)
  { match tag, fs with
    | None, (Some (Some p, _), _) -> p
    | None, (_, (Ftuple _ as fs)) -> Ptuple (Some Anon_tag, fs)
    | tag, (_, fs) -> Ptuple (tag, fs) }

typolybounds:
| LBRACK; t = separated_list(COMMA, typolybound); RBRACK
  { t }

%inline
tytagargs:
| HASH; tag = loc(USYMBOL)
  { Struct_tag tag, [] }
| HASH
  { Anon_tag, [] }
| tag = loc(USYMBOL)
  { Named_tag tag, [] }
| tag = loc(USYMBOL); LBRACK; args = separated_list(COMMA, tyarg); RBRACK
  { Named_tag tag, args }

tyatomic: t = mayloc(tyatomic_) { t }
%inline tyatomic_:
| T_ANY
  { Ttop }
| T_NOTHING
  { Tbot }
| t = symbol
  { Ttyvar t }
| t = tytagargs
  { Trecord (Some (fst t), snd t, empty_fields) }

tyexp: t = mayloc(tyexp_) { t }
tyexp_:
| tagargs = ioption(tytagargs); fs = fields_braces(tyexp)
  { match tagargs, fs with
    | None, fs -> Trecord (None, [], fs)
    | Some (tag, args), fs -> Trecord (Some tag, args, fs) }
| t = tyterm_
  { t }
| LPAR; t = fields_paren_items(tyexp); RPAR; ARROW; r = tyexp
  { let (t, _) = t in
    Tfunc (t, r) }
| t = tyatomic; ARROW; r = tyexp
  { Tfunc ([t], r) }
| t1 = tyexp; VBAR; t2 = tyexp
  { Tjoin(t1, t2) }
| t = typolybounds; b = tyexp %prec ARROW (* kinda hack *)
  { Tforall(t, b) }

tyterm: t = mayloc(tyterm_) { t }
tyterm_:
| ty = tyatomic_
  { ty }
| tagargs = ioption(tytagargs); fs = fields_parens(tyexp)
  { match tagargs, fs with
    | None, (Some (Some t, _), _) -> t
    | None, (_, fs) -> Trecord (Some Anon_tag, [], fs)
    | Some (tag, args), (_, fs) -> Trecord (Some tag, args, fs) }

typolybound:
| s = symbol; SUBTYPE; b = tyexp
  { s, Some b }
| s = symbol { s, None }

tyarg: v = loc(tyarg_) { Some (fst v), snd v }
tyarg_:
| t = tyexp
  { Arg_gen t }
| PLUS; t = tyexp
  { Arg_pos t }
| MINUS; t = tyexp
  { Arg_neg t }
| PLUS; pos = tyexp; MINUS; neg = tyexp
| MINUS; neg = tyexp; PLUS; pos = tyexp
  { Arg_both {neg;pos} }

decl: v = mayloc(decl_) { v }
decl_:
| FN; s = symbol; def = fndef
  { Dfn (s, def) }
| TYPE; s = usymbol; ps = decl_ty_params; body = decl_ty_body
  { Dtype(s,ps,body) }

decl_ty_body:
| fs = loc(fields(tyexp))
  { let ((_,fs),loc) = fs in
    Dty_record(fs,loc) }
| LBRACE; ioption(VBAR); vs = separated_nonempty_list(VBAR, decl_ty_variant); RBRACE
  { Dty_variant(vs) }

decl_ty_variant:
| tag = usymbol; fs = loc(fields(tyexp))
  { let ((_,fs),loc) = fs in tag, (fs,loc) }

decl_ty_params:
|
  { [] } 
| LBRACK; ps = separated_list(COMMA, decl_ty_param); RBRACK
  { ps }

decl_ty_param:
| v = option(variance_spec); id = symbol
  { v, id }

variance_spec:
| ZERO            { { occurs_pos = `No; occurs_neg = `No  } }
| MINUS           { { occurs_pos = `No; occurs_neg = `Yes } }
| PLUS PLUS       { { occurs_pos = `Yes; occurs_neg = `No } }
| PLUS PLUS MINUS
| MINUS PLUS PLUS { { occurs_pos = `Yes; occurs_neg = `Yes } }
| PLUS            { { occurs_pos = `Strict; occurs_neg = `No } }
| PLUS MINUS
| MINUS PLUS      { { occurs_pos = `Strict; occurs_neg = `Yes } }
