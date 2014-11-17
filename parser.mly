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
%token LET
%token IN
%token ASC

%token SUBSUME
%token TOP
%token BOT

%right EQUALS
%right ARROW
%right TY_MEET
%right TY_JOIN

%{
  open Types 
  open Program
%}

%start <Program.typing> prog
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


exp:
| FUN; v = IDENT; ARROW; e = exp 
    { let v = Symbol.intern v in
      fun gamma ->
      let singleton = compile_terms (fun f -> {
          environment = SMap.singleton v (f Neg (TVar "a"));
          expr = f Pos (TVar "a")}) in
      let eG = e (SMap.add v singleton gamma) in
            
      let var = try [SMap.find v eG.environment, TVar "a"] with Not_found -> [] in
      { environment = SMap.remove v eG.environment;
        expr = constrain ((eG.expr, TVar "b") :: var) Pos (ty_fun (TVar "a") (TVar "b")) } }
| LET; v = IDENT; EQUALS; e1 = exp; IN; e2 = exp
    { let v = Symbol.intern v in
      fun gamma ->
      let e1G = e1 gamma in
      let e2G = e2 (SMap.add v e1G gamma) in
      (* CBV soundness: use e1G even if v is unused *)
      { environment = env_join e2G.environment e1G.environment;
        expr = e2G.expr } }
| e = app { e }



app:
| t = term { t }
| f = app; x = term 
    { fun gamma ->
      let fG = f gamma and xG = x gamma in
      { environment = env_join fG.environment xG.environment;
        expr = constrain [fG.expr, ty_fun (TVar "a") (TVar "b");
                          xG.expr, TVar "a"] Pos (TVar "b") } }

term:
| v = IDENT 
    { fun gamma -> clone_scheme (SMap.find (Symbol.intern v) gamma) }
| LPAR; e = exp; RPAR { e }
| LPAR; e = exp; ASC; t = typeterm; RPAR { fun gamma -> ascription (e gamma) t }
| LPAR; RPAR { fun gamma -> { environment = SMap.empty; expr = constrain [] Pos ty_unit } }


subsumption:
| t1 = typeterm; SUBSUME; t2 = typeterm; EOF { (t1, t2) }

onlytype:
| t = typeterm; EOF { t }


typeterm:
| v = IDENT { TVar v }
| t1 = typeterm; ARROW ; t2 = typeterm  { ty_fun t1 t2 }
| TOP { ty_zero }
| BOT { ty_zero }
| UNIT { ty_unit }
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
