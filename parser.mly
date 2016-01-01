%token <Symbol.t> IDENT
%token <int> INT
%token ARROW
%token FUN

%token EOF
%token NL
%token LPAR
%token RPAR
%token LBRACE
%token RBRACE
%token LBRACK
%token RBRACK

%token DEF
%token END

%token COMMA
%token SEMI
%token UNIT
%token TY_MEET
%token TY_JOIN
%token EQUALS
%token REC
%token LET
%token IN
%token ASC
%token DOT
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE

%token EQEQUALS
%token CMP_LT
%token CMP_GT
%token CMP_LTE
%token CMP_GTE
%token OP_ADD
%token OP_SUB
%token UNDER

%token CONS
%token MATCH
%token WITH
%token LIST

%token SUBSUME
%token TOP
%token BOT

%right EQUALS
%right ARROW
%right TY_MEET
%right TY_JOIN

%nonassoc EQEQUALS
%nonassoc CMP_LT
%nonassoc CMP_GT
%nonassoc CMP_LTE
%nonassoc CMP_GTE
%left OP_ADD
%left OP_SUB
%right CONS
%right SEMI

%{
  open Types 
  open Typecheck
  open Exp
  open Location
%}

%start <Exp.exp> prog
%start <Exp.modlist> modlist
%start <Types.var Types.typeterm> onlytype
%start <Types.var Types.typeterm * Types.var Types.typeterm> subsumption

%parameter <L : Location.Locator>

%%

%inline located(X): e = X { (L.pos ($startpos(e), $endpos(e)), e) }
%inline mayfail(X): e = X { Some e } | error { None }
%inline nofail(X): e = X { Some e }

prog:
 e = exp; EOF { e }

nl: NL+ { () }
onl: NL* { () }

modlist:
| onl; e = nonempty_list(moditem_nl); EOF { e}
| onl; EOF { [] }

moditem_nl: e = located(moditem); onl { e } 

moditem:
| LET; v = IDENT; EQUALS; onl; e = exp { MLet (v, e) }
| DEF; f = IDENT; p = params; onl; e = block; END { MDef (f, p, e) }

block_r:
| e = exp_r; onl
    { e }
| e1 = located(mayfail(exp_r)); nl; e2 = block
    { Seq (e1, e2) }

block:
| b = located(mayfail(block_r))
    { b }


exp_r:
| FUN; p = params; ARROW; onl; e = exp 
    { Lambda (p, e) }
| LET; v = IDENT; EQUALS; e1 = exp; IN; e2 = exp
    { Let (v, e1, e2) }
| IF; cond = exp; THEN; tcase = exp; ELSE; fcase = exp
    { If (cond, tcase, fcase) }
| MATCH; e = term; WITH; 
    LBRACK; RBRACK; ARROW; n = exp; 
    TY_JOIN; x = IDENT; CONS; xs = IDENT; ARROW; c = exp
    { Match (e, n, x, xs, c) }
(*| e1 = exp; SEMI; e2 = exp
    { Seq (e1, e2) }*)
| e = simple_exp_r
    { e }

exp:
| e = located(mayfail(exp_r))
    { e }

params: LPAR; p = separated_list(COMMA, located(param)); RPAR { p }

param:
| v = IDENT
    { Ppositional v }
| v = IDENT; EQUALS; UNDER
    { Preq_keyword v }
| v = IDENT; EQUALS; e = exp
    { Popt_keyword (v, e) }

argument:
| e = exp
    { Apositional e }
| v = IDENT; EQUALS; e = exp
    { Akeyword (v, e) }


simple_exp_r:
| e1 = simple_exp; op = binop; e2 = simple_exp
    { App((L.pos ($startpos(op), $endpos(op)), Some (Var (Symbol.intern op))), [(L.pos ($startpos(e1), $endpos(e1)), Apositional e1); (L.pos ($startpos(e1), $endpos(e2)), Apositional e2)]) }
| x = term; CONS; xs = simple_exp
    { Cons(x, xs) }
| e = term_r
    { e }

simple_exp:
| e = located(mayfail(simple_exp_r))
    { e }

%inline binop:
| EQEQUALS { "(==)" }
| CMP_LT   { "(<)" }
| CMP_GT   { "(>)" }
| CMP_LTE  { "(<=)" }
| CMP_GTE  { "(>=)" }
| OP_ADD   { "(+)" }
| OP_SUB   { "(-)" }

term_r:
| v = IDENT 
    { Var v }
| LPAR; e = exp_r; RPAR
    { e }
| LPAR; e = exp; ASC; t = typeterm; RPAR
    { Ascription (e, t) }
| f = term; LPAR; x = separated_list(COMMA, located(argument)); RPAR
    { App (f, x) }
| LPAR; RPAR
    { Unit }
| LBRACE; o = obj; RBRACE
    { Object o }
| LBRACK; RBRACK
    { Nil }
| LBRACK; e = nonemptylist_r; RBRACK
    { e }
| e = term; DOT; f = IDENT
    { GetField (e, f) }
| i = INT
    { Int i }
| TRUE
    { Bool true }
| FALSE
    { Bool false }

term:
| t = located(mayfail(term_r))
    { t }

obj:
| v = IDENT; EQUALS; e = exp
    { [v, e] }
| v = IDENT; EQUALS; e = exp; SEMI; o = obj
    { (v, e) :: o }

nonemptylist_r:
| x = exp
    { Cons(x, (let (l, _) = x in l, Some Nil)) }
| x = exp; COMMA; xs = nonemptylist
    { Cons(x, xs) }

%inline nonemptylist:
| e = located(nofail(nonemptylist_r))
    { e }

subsumption:
| t1 = typeterm; SUBSUME; t2 = typeterm; EOF { (t1, t2) }

onlytype:
| t = typeterm; EOF { t }


typeterm:
| v = IDENT {
  let t = match Symbol.to_string v with
    | "int" | "unit" | "bool" -> ty_base v
    | s -> ty_var s in
  t  (L.pos ($startpos, $endpos))}
(* | t1 = typeterm; ARROW ; t2 = typeterm  { ty_fun (fun _ -> t1) (fun _ -> t2) (L.pos ($startpos, $endpos)) } *)
| TOP { ty_zero (L.pos ($startpos, $endpos)) }
| BOT { ty_zero (L.pos ($startpos, $endpos)) }
| LPAR; t = typeterm; LIST; RPAR { ty_list (fun _ -> t) (L.pos ($startpos, $endpos)) }
| UNIT { ty_base (Symbol.intern "unit") (L.pos ($startpos, $endpos)) }
| t1 = typeterm; meetjoin; t2 = typeterm { TAdd (t1, t2)  } %prec TY_MEET
| REC; v = IDENT; EQUALS; t = typeterm { TRec (Symbol.to_string v, t) }
| LPAR; t = typeterm; RPAR { t }

%inline meetjoin : TY_MEET | TY_JOIN {}
