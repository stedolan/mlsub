type 'a located = Location.t * 'a



type tyvar = string

type typaram =
| PPos of Symbol.t
| PNeg of Symbol.t
| PPosNeg of Symbol.t

type tyarg =
| APos of typeterm
| ANeg of typeterm
| AUnspec of typeterm
| ANegPos of typeterm * typeterm

and typeterm =
| TZero of Typector.polarity
| TNamed of tyvar * tyarg list
| TCons of typeterm Typector.Components.t
| TAdd of Typector.polarity * typeterm * typeterm
| TRec of tyvar * typeterm



type rparam =
| Ppositional of Symbol.t
| Preq_keyword of Symbol.t
| Popt_keyword of Symbol.t * exp
and param = rparam located

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
  | Ascription of exp * typeterm
  | Unit
  | Int of int
  | Bool of bool
  | If of exp * exp * exp
  | Nil
  | Cons of exp * exp
  | Match of exp * exp * Symbol.t * Symbol.t * exp
  | Object of (Symbol.t * exp) list
  | GetField of exp * Symbol.t

and exp = rexp option located

and moditem =
  | MType of Symbol.t * typaram list * typeterm
  | MDef of Symbol.t * param list * exp
  | MLet of Symbol.t * exp

and modlist = moditem located list


