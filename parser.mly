%token <string> IDENT
%token ARROW
%token FUN

%token EOF
%token LPAR
%token RPAR
%token UNIT
%token TY_MEET
%token TY_JOIN
%token EQUALS
%token REC

%token SUBSUME


%right EQUALS
%right ARROW
%right TY_MEET
%right TY_JOIN

%{
  open Types 
  open Program
%}

%start <Program.scheme> prog
%start <Types.var Types.typeterm> onlytype
%start <Types.var Types.typeterm * Types.var Types.typeterm> subsumption

%{
(*  let env_join = Intmap.union_with (fun a b -> constrain [a, TVar "a"; b, TVar "a"] Neg (TVar "a")) *)
  let env_join = SMap.merge (fun k a b -> match a, b with
    | (None, x) | (x, None) -> x
    | Some a, Some b ->
      Some (constrain [a, TVar "a"; b, TVar "a"] Neg (TVar "a")))
%}
%%

prog:
| e = exp; EOF { e }

(* wrong *)
exp:
| FUN; v = IDENT; ARROW; e = exp 
    { let v = Symbol.intern v in
      let var = try [SMap.find v e.environment, TVar "a"] with Not_found -> [] in
      { environment = SMap.remove v e.environment;
        expr = constrain ((e.expr, TVar "b") :: var) Pos (TCons (Func (TVar "a", TVar "b"))) } }
| e = app { e }



app:
| t = term { t }
| f = app; x = term 
    { { environment = env_join f.environment x.environment;
        expr = constrain [f.expr, TCons (Func (TVar "a", TVar "b"));
                          x.expr, TVar "a"] Pos (TVar "b") } }

term:
| v = IDENT 
    { compile_terms (fun f -> {
      environment = SMap.singleton (Symbol.intern v) (f Neg (TVar "a"));
      expr = f Pos (TVar "a")}) }
| LPAR; e = exp; RPAR { e }



subsumption:
| t1 = typeterm; SUBSUME; t2 = typeterm; EOF { (t1, t2) }

onlytype:
| t = typeterm; EOF { t }

typeterm:
| v = IDENT { TVar v }
| t1 = typeterm; ARROW ; t2 = typeterm  { TCons (Func (t1, t2)) }
| UNIT { TCons Unit }
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