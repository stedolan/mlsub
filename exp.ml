type 'a located = Location.t * 'a



type tyvar = Symbol.t

type typaram =
| TParam of Variance.variance option * Symbol.t

type tyarg =
| APos of typeterm
| ANeg of typeterm
| AUnspec of typeterm
| ANegPos of typeterm * typeterm

and typeterm =
| TZero of Variance.polarity
| TNamed of tyvar * tyarg list
| TCons of typeterm Typector.Components.t
| TAdd of Variance.polarity * typeterm * typeterm
| TRec of tyvar * typeterm



type rparam =
| Ppositional of Symbol.t
| Preq_keyword of Symbol.t
| Popt_keyword of Symbol.t * exp
and param = (rparam * typeterm option) located

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
  | Typed of exp * typeterm
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


