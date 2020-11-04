: int <: int
> ok

: int <: bool
> typechecking error: Failure("incompat")

: [A] (A) -> A <: (int) -> int
> ok

: (int) -> int <: [A] (A) -> A
> typechecking error: Failure("incompat")

: [A,B,C, A <: C, B <: C] (A, B) -> C <: [X] (X, X) -> X
> ok

: [X] (X, X) -> X <: [A,B,C, A <: C, B <: C] (A, B) -> C
> ok

: [X] {foo: (X) -> X, bar: (X) -> X} <: {foo: (int) -> int, bar: (int) -> int}
> ok

: [X] {foo: (X) -> X, bar: (X) -> X} <: [X <: int] {foo: (X) -> int, bar: (X) -> X}
> ok

: [X] {foo: (X) -> X, bar: (X) -> X} <: {foo: (int) -> int, bar: (string) -> string}
> typechecking error: Failure("incompat")

: [X] {foo: (X) -> X, bar: (X) -> X} <: [X, Y] {foo: (X) -> X, bar: (Y) -> Y}
> typechecking error: Failure("incompat")

: [X, Y] {foo: (X) -> X, bar: (Y) -> Y} <: [X] {foo: (X) -> X, bar: (X) -> X}
> ok

: [X <: int, X :> int] (X) -> X <: (int) -> int
> ok

: [X <: int, Y :> int] (X) -> Y <: (int) -> int
> ok

: (int) -> int <: [] (int) -> int
> ok

: [A <: int] (A) -> (int, ([B] (A) -> A)) <: (int) -> (int, [A <: int] (A) -> A)
> typechecking error: Failure("incompat")

: (int) -> (int, [A <: int] (A) -> A) <: [A <: int] (A) -> (int, ([B] (A) -> A))
> ok

: [B <: int] (B) -> B <: [A <: int] ([C] (A) -> A)
> ok

# FIXME: check Mitchell's distrib & other quantifier-pushing relations
