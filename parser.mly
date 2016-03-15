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
%token TYPE
%token END

%token COMMA
%token SEMI
%token AND
%token OR
%token EQUALS
%token REC
%token LET
%token IN
%token COLON
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
%token PLUS
%token MINUS
%token UNDER
%token ANY
%token NOTHING

%token CONS
%token MATCH
%token WITH

%token SUBSUME


%right EQUALS
%right ARROW
%right AND
%right OR

%nonassoc EQEQUALS
%nonassoc CMP_LT
%nonassoc CMP_GT
%nonassoc CMP_LTE
%nonassoc CMP_GTE
%left PLUS
%left MINUS
%right CONS

%{
  open Variance
  open Typector
  open Types 
  open Typecheck
  open Exp
  open Location
%}

%start <Exp.exp> prog
%start <Exp.modlist> modlist
%start <Typector.typeterm> onlytype
%start <Typector.typeterm * Typector.typeterm> subsumption

%parameter <L : Location.Locator>

%%

%inline located(X): e = X { (L.pos ($startpos(e), $endpos(e)), e) }
%inline mayfail(X): e = X { Some e } | error { None }
%inline nofail(X): e = X { Some e }

prog:
 e = exp; EOF { e }

onl: NL* { () }

snl:
| NL; onl { () }
| onl; SEMI; onl { () }

(* List with optional trailing seperator and error handling *)
sep_list(Sep, Item):
|
  { [] }
| x = Item { [x] }
| x = Item; Sep; xs = sep_list(Sep, Item) { x :: xs }
| error; Sep; xs = sep_list(Sep, Item) { xs }


modlist:
| onl; e = sep_list(snl, located(moditem));  EOF { e }



moditem:
| LET; v = IDENT; EQUALS; onl; e = exp { MLet (v, e) }
| DEF; f = IDENT; p = params; onl; e = block; END { MDef (f, p, e) }
| DEF; f = IDENT; p = params; COLON; t = typeterm; snl; e = block; END { MDef (f, p, (L.pos ($startpos(t), $endpos(e)), Some (Typed(e, t)))) }
| TYPE; n = IDENT; args = loption(delimited(LBRACK, 
                            separated_nonempty_list(COMMA, typeparam), RBRACK));
  EQUALS; t = typeterm
    { MType (n, args, t) }
| TYPE; n = IDENT; args = loption(delimited(LBRACK, 
                            separated_nonempty_list(COMMA, typeparam), RBRACK));
    { MOpaqueType (n, args) }


block_r:
| e = exp_r; onl
    { e }
| e1 = located(mayfail(exp_r)); snl; e2 = block
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
    OR; x = IDENT; CONS; xs = IDENT; ARROW; c = exp
    { Match (e, n, x, xs, c) }
(*| e1 = exp; SEMI; e2 = exp
    { Seq (e1, e2) }*)
| e = simple_exp_r
    { e }

exp:
| e = located(mayfail(exp_r))
    { e }

params: LPAR; p = separated_list(COMMA, located(paramtype)); RPAR { p }

paramtype:
| p = param
    { p, None }
| p = param; COLON; t = typeterm
    { p, Some t }

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
| PLUS     { "(+)" }
| MINUS    { "(-)" }

term_r:
| v = IDENT 
    { Var v }
| LPAR; e = exp_r; RPAR
    { e }
| LPAR; e = exp; COLON; t = typeterm; RPAR
    { Typed (e, t) }
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

variance:
| PLUS { VPos }
| MINUS { VNeg }
| PLUS; MINUS { VNegPos }
| MINUS; PLUS { VNegPos }

typearg:
| PLUS; t = typeterm { VarSpec (APos t) }
| MINUS; t = typeterm { VarSpec (ANeg t) }
| MINUS; s = typeterm; PLUS; t = typeterm
| PLUS; t = typeterm; MINUS; s = typeterm { VarSpec (ANegPos (s, t)) }
| t = typeterm { VarUnspec t }

typeparam:
| v = option(variance); x = IDENT { TParam (v, x) }
| UNDER { TNoParam }

objtype:
| v = IDENT; COLON; t = typeterm
   { (v, fun _ -> t) }

(* FIXME: detect duplicate parameters *)
funtype:
| RPAR; { [] }
| t = typeterm; COMMA; ts = funtype { (None, t) ::  ts }
| t = typeterm; RPAR { [None, t] }
| v = IDENT; COLON; t = typeterm; COMMA; ts = funtype { (Some v, t) :: ts }
| v = IDENT; COLON; t = typeterm; RPAR { [Some v, t] }

typeterm:
| v = IDENT; LBRACK; ps = separated_nonempty_list(COMMA, typearg); RBRACK
     { TNamed (v, ps) }
| v = IDENT
     { TNamed (v, []) }
(* funtype includes its closing paren as a hack to avoid a conflict *)
| LPAR; ts = funtype; ARROW; tr = typeterm 
    { TCons (ty_fun
        (ts |> List.filter (function (None, _) -> true | _ -> false) |> List.map (fun (_, t) -> fun _ -> t))
        (ts |> List.fold_left (fun s (v, t) -> match v with Some v -> Typector.SMap.add v ((fun _ -> t), true) s | None -> s) Typector.SMap.empty)
        (fun _ -> tr)
        (L.pos ($startpos, $endpos))) }
| ANY { TZero Neg }
| NOTHING { TZero Pos }
| LBRACE; o = separated_list(COMMA, objtype); RBRACE 
  { TCons (ty_obj_l o (L.pos ($startpos, $endpos))) }
| t1 = typeterm; p = meetjoin; t2 = typeterm { TAdd (p, t1, t2)  } %prec AND
| REC; v = IDENT; EQUALS; t = typeterm { TRec (v, t) }
| UNDER { TWildcard }
| LPAR; t = typeterm; RPAR { t }

%inline meetjoin : AND { Variance.Neg } | OR { Variance.Pos }
