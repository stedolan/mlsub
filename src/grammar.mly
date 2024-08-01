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
%token FN LET TRUE FALSE IF ELSE TILDE HASH
%token SUBTYPE SUPTYPE AT
%token MATCH

%nonassoc low_priority
%nonassoc ARROW
%nonassoc LPAR LBRACE
%left VBAR                      (* FIXME VBAR vs AT precedence? *)
%right SEMI
(*%nonassoc high_priority*)

%{ open Tuple_fields open Exp open Location %}
%start <[`Exp of Exp.exp | `Sub of Exp.tyexp * Exp.tyexp]> prog

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

prog:
| e = exp; EOF { `Exp e }
| COLON; t1 = tyexp; SUBTYPE; t2 = tyexp; EOF { `Sub (t1, t2) }

symbol: s = loc(SYMBOL) { s }
usymbol: s = loc(USYMBOL) { s }

struct_tag: s = loc(struct_tag_) { (s : string loc) }
struct_tag_:
| s = QUSYMBOL { s }
(*| HASH { "" }
| HASH; s = USYMBOL { s }*)

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

%inline mand_flag:
|
  { Mandatory }
| QUESTION
  { Optional }

field_name:
| f = SYMBOL
  { Field_named f }
| f = INT
  { Field_positional f }

%inline ext_dots:
|      { Ext_closed }
| DOTS { Ext_open }

fields_paren_items1(X):
| DOTS
  { [], Ext_open }
| f = X; ioption(COMMA)
  { [f], Ext_closed }
| f = X; COMMA; fs = fields_paren_items1(X)
  { (f::fst fs), snd fs }

fields_paren_items(X):
| e = ext_dots
  { [], false, e }
| f = X; c = ioption(COMMA)
  { [f], Option.is_some c, Ext_closed }
| f = X; COMMA; fs = fields_paren_items1(X)
  { (f::fst fs), false, snd fs }

fields_brace_item(X):
| f = loc(field_name); m = mand_flag; COLON; e = X
  { f, m, Some e }
| f = loc(field_name); m = mand_flag
  { f, m, None }

fields_brace_items1(X):
| DOTS
  { [], Ext_open }
| f = fields_brace_item(X); ioption(COMMA)
  { [f], Ext_closed }
| f = fields_brace_item(X); COMMA; fs = fields_brace_items1(X)
  { (f::fst fs), snd fs }

fields_brace_items(X):
| 
  { [], Ext_closed }
| fs = fields_brace_items1(X)
  { fs }

fields(X):
| LPAR; xs = fields_paren_items(X); RPAR
  { match xs with
    | [x] as xs, false, e -> Some x, Ftuple (xs, e)
    | xs, _, e -> None, Ftuple (xs, e) }
| LBRACE; xs = fields_brace_items(X); RBRACE
  { None, Frecord (fst xs, snd xs) }

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
  ty = ioption(ARROW; t = tyexp {t});
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
| tag = usymbol %prec low_priority
  { Some (Tuple (Some tag, Ftuple ([], Ext_closed))) }
| LPAR; e = exp; COLON; t = tyexp; RPAR
  { Some (Typed (e, t)) }
| tag = ioption(usymbol); fs = fields(exp)
  { match tag, fs with
    | None, (Some (Some e, _), _) -> Some e
    | None, (Some (None, _), _) -> None
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
| tag = usymbol
  { Ptuple (Some tag, Ftuple ([], Ext_closed)) }
| tag = ioption(usymbol); fs = fields(pat)
  { match tag, fs with
    | None, (Some (Some p, _), _) -> p
    | tag, (_, fs) -> Ptuple (tag, fs) }

typolybounds:
| LBRACK; t = separated_list(COMMA, typolybound); RBRACK
  { t }

tyexp: t = mayloc(tyexp_) { t }
tyexp_:
| t = anyident
  { Tnamed t }
| tag = struct_tag %prec low_priority
  { Trecord(Some tag, Ftuple ([], Ext_closed)) }
| tag = ioption(struct_tag); t = fields(tyexp)
  { match tag, t with
    | None, (Some (Some t, _), _) -> t
    | tag, (_, fs) -> Trecord (tag, fs) }
(* FIXME: what does (...) -> a | b mean? (prec of -> and |) *)
| LPAR; t = fields_paren_items(tyexp); RPAR; ARROW; r = tyexp
  { let (t, _, _FIXME_e) = t in
    Tfunc (t, r) }
| t1 = tyexp; VBAR; t2 = tyexp
  { Tjoin(t1, t2) }
| t = typolybounds; b = tyexp %prec ARROW (* kinda hack *)
  { Tforall(t, b) }

typolybound:
| s = anysymbol; SUBTYPE; b = tyexp
  { s, Some b }
| s = anysymbol { s, None }
