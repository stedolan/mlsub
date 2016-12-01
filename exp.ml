type 'a located = Location.t * 'a




type rparam =
| Ppositional of Symbol.t
| Preq_keyword of Symbol.t
| Popt_keyword of Symbol.t * exp
and param = (rparam * Typector.typeterm option) located

and rargument =
| Apositional of exp
| Akeyword of Symbol.t * exp
and argument = rargument located

and rexp =
  | Var of Symbol.t
  | Lambda of param list * exp
  | Let of Symbol.t * exp * exp
  | Rec of Symbol.t * exp
  | App of exp * argument list
  | Seq of exp * exp
  | Typed of exp * Typector.typeterm
  | Unit
  | Int of int
  | String of string
  | Bool of bool
  | If of exp * exp * exp
  | Nil
  | Cons of exp * exp
  | Match of exp list * (pat list located * exp) list
  | Object of Symbol.t option * (Symbol.t * exp) list
  | GetField of exp * Symbol.t

and exp = rexp option located

and rpat =
  | PNone
  | PWildcard
  | PVar of Symbol.t
  | PObject of Symbol.t option * (Symbol.t * pat) list
  | PInt of int
  | PAlt of pat * pat

and pat = rpat option located


and moditem =
  | MType of Symbol.t * Typector.typaram list * Typector.typeterm
  | MOpaqueType of Symbol.t * Typector.typaram list
  | MDef of Symbol.t * param list * exp
  | MLet of Symbol.t * exp

and modlist = moditem located list
