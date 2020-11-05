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



# poly!
fn[A](x : A) { x }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

fn[A,B](id : [A](A) -> A, (x,y):(A, B)) { (id(y),id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.0, .0.1)) → (.0.1, .0.0)

fn(id : [A](A) -> A, (x,y)) { (id(y),id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.1, .0.0)) → (.0.0, .0.1)

fn[A](x : A) { if x.cond {x} else {x} }
> typechecking error: Failure("incompat")

fn[A <: {cond:bool}](x : A) { if x.cond {x} else {x} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool)]. (.0.0) → .0.0

fn(f) { fn[A](x : A) { f(x) } }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((⊤) → .0.0) → ∀⁺ 0:[⊥,⊤]. (.0.0) → .1.0

# bidir poly functions

(fn (x: A) { x } : [A] (A) -> A)
> typechecking error: Failure("unknown type A")

(fn (x: bool) { x } : [A] (A) -> A)
> typechecking error: Failure("incompat")

(fn (x: any) { x } : [A] (A) -> A)
> typechecking error: Failure("incompat")

(fn[B] (x: B) { x } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

(fn[B] (x) { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

(fn[B] (x) : B { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

fn[B <: {foo:int}] (x) : B { x }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0

fn[B <: {foo:int}] (x) { (x : B) }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0

(fn() { @true } : [A]() -> bool)
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → bool

fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; ch
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; fn (a,b) { ch(a, b) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0

(fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0

(fn[A,B,R, A<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> typechecking error: Failure("incompat")

(fn[A,B,R, A<:R](x : A, y : B) : R { x } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0

let wid = fn (id: [B,A <: {foo:B}](A) -> B) { id({foo:5}) }; fn(f) { wid(fn(x){let z = f(x); x}) }
> internal error: approx unimplemented
> Raised at Lang__Types.intfail in file "src/types.ml", line 5, characters 16-34
> Called from Stdlib__map.Make.mapi in file "map.ml", line 312, characters 19-24
> Called from Lang__Tuple_fields.map_fields in file "src/tuple_fields.ml", line 50, characters 13-67
> Called from Lang__Typedefs.map_head in file "src/typedefs.ml", line 238, characters 28-56
> Called from Lang__Types.approx_styp in file "src/types.ml", line 269, characters 13-57
> Called from Lang__Types.subtype_styp_vars.(fun) in file "src/types.ml", line 364, characters 33-70
> Called from Lang__Intlist.iter in file "src/intlist.ml", line 90, characters 21-26
> Called from Lang__Types.subtype_styp_vars in file "src/types.ml", line 362, characters 5-151
> Called from Lang__Types.subtype_styp_vars.(fun) in file "src/types.ml", line 388, characters 7-56
> Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
> Called from Lang__Types.subtype_styp in file "src/types.ml", line 394, characters 10-30
> Called from Lang__Check.check' in file "src/check.ml", line 249, characters 5-23
> Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
> Called from Lang__Tuple_fields.fold_fields in file "src/tuple_fields.ml", line 54, characters 12-65
> Called from Lang__Check.infer' in file "src/check.ml", line 326, characters 5-62
> Called from Lang__Check.infer in file "src/check.ml", line 254, characters 26-43
> Called from Lang__Check.check' in file "src/check.ml", line 231, characters 15-44
> Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
> Called from Lang__Tuple_fields.fold_fields in file "src/tuple_fields.ml", line 54, characters 12-65
> Called from Lang__Check.infer' in file "src/check.ml", line 326, characters 5-62
> Called from Lang__Check.infer in file "src/check.ml", line 254, characters 26-43
> Called from Lang__Check.infer' in file "src/check.ml", line 303, characters 15-48
> Called from Lang__Check.infer in file "src/check.ml", line 254, characters 26-43
> Called from Lang__Check.infer in file "src/check.ml", line 254, characters 26-43
> Called from Dune__exe__Test_runner.run_cmd in file "test/test_runner.ml", line 39, characters 12-36
> 

let id = fn(x) { x }; id (id)
> internal error: approx unimplemented
> Raised at Lang__Types.intfail in file "src/types.ml", line 5, characters 16-34
> Called from Lang__Typedefs.map_head in file "src/typedefs.ml", line 240, characters 46-55
> Called from Lang__Types.approx_styp in file "src/types.ml", line 269, characters 13-57
> Called from Lang__Types.subtype_styp_vars.(fun) in file "src/types.ml", line 364, characters 33-70
> Called from Lang__Intlist.iter in file "src/intlist.ml", line 90, characters 21-26
> Called from Lang__Types.subtype_styp_vars in file "src/types.ml", line 362, characters 5-151
> Called from Lang__Types.subtype_styp in file "src/types.ml", line 394, characters 10-30
> Called from Lang__Check.check' in file "src/check.ml", line 249, characters 5-23
> Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
> Called from Lang__Tuple_fields.fold_fields in file "src/tuple_fields.ml", line 54, characters 12-65
> Called from Lang__Check.infer' in file "src/check.ml", line 326, characters 5-62
> Called from Lang__Check.infer in file "src/check.ml", line 254, characters 26-43
> Called from Lang__Check.infer in file "src/check.ml", line 254, characters 26-43
> Called from Dune__exe__Test_runner.run_cmd in file "test/test_runner.ml", line 39, characters 12-36
> 
