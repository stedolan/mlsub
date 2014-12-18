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

%token SUBSUME
%token TOP
%token BOT

%right EQUALS
%right ARROW
%right TY_MEET
%right TY_JOIN

%{
  open Types 
  open Typecheck
  open Exp
%}

%start <Exp.exp> prog
%start <Types.var Types.typeterm> onlytype
%start <Types.var Types.typeterm * Types.var Types.typeterm> subsumption


%%

prog:
| e = exp; EOF { e }


exp:
| FUN; v = IDENT; ARROW; e = exp 
    { Lambda (Symbol.intern v, e) }
| LET; v = IDENT; EQUALS; e1 = exp; IN; e2 = exp
    { Let (Symbol.intern v, e1, e2) }
| e = app
    { e }


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
| UNIT { ty_unit () }
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
