type 'a arguments = 'a
type exp =
  | Var of Symbol.t
  | Lambda of Symbol.t arguments * exp
  | Let of Symbol.t * exp * exp
  | App of exp * exp arguments
  | Ascription of exp * Types.var Types.typeterm
  | Unit
  | Int of int
  | Object of (Symbol.t * exp) list
  | GetField of exp * Symbol.t


