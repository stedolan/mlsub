%token <string> IDENT
%token <int> INT
%token ARROW
%token FUN

%token EOF
%token LPAR
%token RPAR
%token LBRACE
%token RBRACE
%token COMMA
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

%token NIL
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

%{
  open Types 
  open Typecheck
  open Exp
%}

%start <Exp.exp> prog
%start <(string * Exp.exp) list> modlist
%start <Types.var Types.typeterm> onlytype
%start <Types.var Types.typeterm * Types.var Types.typeterm> subsumption


%%

prog:
| e = exp; EOF { e }

modlist:
| EOF { [] }
| LET; v = IDENT; EQUALS; e = exp; m = modlist; { (v,e) :: m }
| LET; REC; v = IDENT; EQUALS; e = exp; m = modlist; { (v,Rec(Symbol.intern v, e)) :: m }

exp:
| FUN; v = IDENT; ARROW; e = exp 
    { Lambda (Symbol.intern v, e) }
| LET; v = IDENT; EQUALS; e1 = exp; IN; e2 = exp
    { Let (Symbol.intern v, e1, e2) }
| LET; REC; v = IDENT; EQUALS; e1 = exp; IN; e2 = exp
    { Let (Symbol.intern v, Rec (Symbol.intern v, e1), e2) }
| IF; cond = exp; THEN; tcase = exp; ELSE; fcase = exp
    { If (cond, tcase, fcase) }
| MATCH; e = term; WITH; 
    NIL; ARROW; n = exp; 
    TY_JOIN; x = IDENT; CONS; xs = IDENT; ARROW; c = exp
    { Match (e, n, Symbol.intern x, Symbol.intern xs, c) }
| e = simple_exp
    { e }

simple_exp:
| e1 = simple_exp; op = binop; e2 = simple_exp
    { App(App(Var (Symbol.intern op), e1), e2) }
| x = app; CONS; xs = simple_exp
    { Cons(x, xs) }
| e = app
    { e }

%inline binop:
| EQUALS   { "(=)" }
| EQEQUALS { "(==)" }
| CMP_LT   { "(<)" }
| CMP_GT   { "(>)" }
| CMP_LTE  { "(<=)" }
| CMP_GTE  { "(>=)" }
| OP_ADD   { "(+)" }
| OP_SUB   { "(-)" }

app:
| t = term
    { t }
| f = app; x = term 
    { App (f, x) }


term:
| v = IDENT 
    { Var (Symbol.intern v) }
| LPAR; e = exp; RPAR
    { e }
| LPAR; e = exp; ASC; t = typeterm; RPAR
    { Ascription (e, t) }
| LPAR; RPAR
    { Unit }
| LBRACE; o = obj; RBRACE
    { Object o }
| e = term; DOT; f = IDENT
    { GetField (e, Symbol.intern f) }
| i = INT
    { Int i }
| NIL
    { Nil }
| TRUE
    { Bool true }
| FALSE
    { Bool false }


obj:
| v = IDENT; EQUALS; e = exp
    { [Symbol.intern v, e] }
| v = IDENT; EQUALS; e = exp; COMMA; o = obj
    { (Symbol.intern v, e) :: o }

subsumption:
| t1 = typeterm; SUBSUME; t2 = typeterm; EOF { (t1, t2) }

onlytype:
| t = typeterm; EOF { t }


typeterm:
| v = IDENT { TVar v }
| t1 = typeterm; ARROW ; t2 = typeterm  { ty_fun t1 t2 }
| TOP { ty_zero }
| BOT { ty_zero }
| LPAR; t = typeterm; LIST; RPAR { ty_list t }
| UNIT { ty_base (Symbol.intern "unit") }
| t1 = typeterm; meetjoin; t2 = typeterm { TAdd (t1, t2) } %prec TY_MEET
| REC; v = IDENT; EQUALS; t = typeterm { TRec (v, t) }
| LPAR; t = typeterm; RPAR { t }

%inline meetjoin : TY_MEET | TY_JOIN {}

(*
prog:
  | v = value { Some v }
  | EOF       { None   } ;

value:
  | LEFT_BRACE; obj = obj_fields; RIGHT_BRACE { `Assoc obj  }
  | LEFT_BRACK; vl = list_fields; RIGHT_BRACK { `List vl    }
  | s = STRING                                { `String s   }
  | i = INT                                   { `Int i      }
  | x = FLOAT                                 { `Float x    }
  | TRUE                                      { `Bool true  }
  | FALSE                                     { `Bool false }
  | NULL                                      { `Null       } ;

obj_fields:
    obj = separated_list(COMMA, obj_field)    { obj } ;

obj_field:
    k = STRING; COLON; v = value              { (k, v) } ;

list_fields:
    vl = separated_list(COMMA, value)         { vl } ;
*)
