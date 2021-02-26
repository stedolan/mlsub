: int <: int
> ok

: int <: bool
> typechecking error: Failure("incompat")

: [A] (A) -> A <: (int) -> int
> ok

: (int) -> int <: [A] (A) -> A
> typechecking error: Failure("incompat")

: [A, B] (A, B) -> (A|B) <: [X] (X, X) -> X
> ok

: [X] (X, X) -> X <: [A, B] (A, B) -> (A|B)
> ok

: [X] () -> {foo: (X) -> X, bar: (X) -> X} <: () -> {foo: (int) -> int, bar: (int) -> int}
> ok

: [X] () -> {foo: (X) -> X, bar: (X) -> X} <: [X <: int] () -> {foo: (X) -> int, bar: (X) -> X}
> ok

: [X] () -> {foo: (X) -> X, bar: (X) -> X} <: () -> {foo: (int) -> int, bar: (string) -> string}
> typechecking error: Failure("incompat")

: [X] () -> {foo: (X) -> X, bar: (X) -> X} <: [X, Y] () -> {foo: (X) -> X, bar: (Y) -> Y}
> typechecking error: Failure("incompat")

: [X, Y] () -> {foo: (X) -> X, bar: (Y) -> Y} <: [X] () -> {foo: (X) -> X, bar: (X) -> X}
> ok

# all combinations of int -> int w/ one rigid var

: [X <: int] (X) -> (X|int) <: (int) -> int
> ok
: (int) -> int <: [X <: int] (X) -> (X|int)
> ok

: [X <: int] (X) -> X <: (int) -> int
> ok
: (int) -> int <: [X <: int] (X) -> X
> typechecking error: Failure("incompat")

: [X] (X) -> (X|int) <: (int) -> int
> ok
: (int) -> int <: [X] (X) -> (X|int)
> typechecking error: Failure("incompat")

: [X] (X) -> (X) <: (int) -> int
> ok
: (int) -> int <: [X] (X) -> (X)
> typechecking error: Failure("incompat")



: [X <: int] (X) -> (X|bool) <: (int) -> bool
> typechecking error: Failure("incompat")
: (int) -> bool <: [X <: int] (X) -> (X|bool)
> ok




: [X <: int, Y] (X) -> (Y|int) <: (int) -> int
> ok

: (int) -> int <: [X <: int, Y] (X) -> (Y|int)
> ok

: (int) -> int <: [] (int) -> int
> ok

: [A <: int] (A) -> (int, ([B] (A) -> A)) <: (int) -> (int, [A <: int] (A) -> A)
> typechecking error: Failure("incompat")

: (int) -> (int, [A <: int] (A) -> A) <: [A <: int] (A) -> (int, ([B] (A) -> A))
> ok

: [B <: int] (B) -> B <: [A <: int] (A) -> A
> ok

: [B <: int] (B) -> B <: [A <: int, C] (A) -> A
> ok

# FIXME: check Mitchell's distrib & other quantifier-pushing relations




# scope escape check
: [A] ((A) -> A) -> ((A) -> A) <: ([B](B) -> B) -> ([C](C) -> C)
