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
> fn [A](x: A) { x }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

fn[A,B](id : [A](A) -> A, (x,y):(A, B)) { (id(y),id(x)) }
> fn [A, B](id: [A] (A) -> A, (x, y): (A, B)) { (id(y), id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.0, .0.1)) → (.0.1, .0.0)

fn(id : [A](A) -> A, (x,y)) { (id(y),id(x)) }
> fn (id: [A] (A) -> A, (x, y)) { (id(y), id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.1, .0.0)) → (.0.0, .0.1)

fn[A](x : A) { if x.cond {x} else {x} }
> fn [A](x: A) { if x.cond{x} else {x} }
> typechecking error: Failure("incompat")

fn[A <: {cond:bool}](x : A) { if x.cond {x} else {x} }
> fn [A <: {cond: bool}](x: A) { if x.cond{x} else {x} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool)]. (.0.0) → .0.0

fn(f) { fn[A](x : A) { f(x) } }
> fn (f) { fn [A](x: A) { f(x) } }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((⊤) → .0.0) → ∀⁺ 0:[⊥,⊤]. (.0.0) → .1.0

# bidir poly functions

(fn (x: A) { x } : [A] (A) -> A)
> (fn (x: A) { x } : [A] (A) -> A)
> typechecking error: Failure("unknown type A")

(fn (x: bool) { x } : [A] (A) -> A)
> (fn (x: bool) { x } : [A] (A) -> A)
> typechecking error: Failure("incompat")

(fn (x: any) { x } : [A] (A) -> A)
> (fn (x: any) { x } : [A] (A) -> A)
> typechecking error: Failure("incompat")

(fn[B] (x: B) { x } : [A] (A) -> A)
> (fn [B](x: B) { x } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

(fn[B] (x) { (x : B) } : [A] (A) -> A)
> (fn [B](x) { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

(fn[B] (x) : B { (x : B) } : [A] (A) -> A)
> (fn [B](x) : B { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

fn[B <: {foo:int}] (x) : B { x }
> fn [B <: {foo: int}](x) : B { x }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0

fn[B <: {foo:int}] (x) { (x : B) }
> fn [B <: {foo: int}](x) { (x : B) }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0

(fn() { @true } : [A]() -> bool)
> (fn () { @true } : [A] () -> bool)
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → bool

fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }
> fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; ch
> let ch = fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }; ch
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; fn (a,b) { ch(a, b) }
> let ch = fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }; fn (a, b) { ch(a, b) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0

(fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0

(fn[A,B,R, A<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R](x: A, y: B) : R { if true{x} else {y} } : [A] (A, A) -> A)
> typechecking error: Failure("incompat")

(fn[A,B,R, A<:R](x : A, y : B) : R { x } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R](x: A, y: B) : R { x } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0

let wid = fn (id: [B,A <: {foo:B}](A) -> B) { id({foo:5}) }; fn(f) { wid(fn(x){let z = f({bar:x}); x.foo}) }
> let wid = fn (id: [B, A <: {foo: B}] (A) -> B) { id({foo: 5}) }; fn (f) { wid(fn (x) { let z = f({bar: x}); x.foo }) }
> * ⊢ (((bar: (foo: ⊤))) → ⊤) → int

let id = fn(x) { x }; fn () { (id (id), id) }
> let id = fn (x) { x }; fn () { (id(id), id) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → ((.0.0) → .0.0, ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0)


fn(f) { fn(id: [A] (A) -> A) { let x = f(id); id(1) } }
> fn (f) { fn (id: [A] (A) -> A) { let x = f(id); id(1) } }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (((.0.0) → .0.0) → ⊤) → (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → int

fn(f) { fn(id: [A] (A) -> A) { id(fn(y) { let x = f(y); y }) } }
> fn (f) { fn (id: [A] (A) -> A) { id(fn (y) { let x = f(y); y }) } }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤]. ((.0.0) → ⊤) → ∀⁺ 0:[⊥,.1.0]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → (.0.0) → .0.0


(fn(x) {(fn(y){y})(x)} : [A] (A) -> A)
> (fn (x) { (fn (y) { y })(x) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

let id = fn(y) { y }; (fn[A](x : A) {id(x)})
> let id = fn (y) { y }; (fn [A](x: A) { id(x) })
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

let id = fn(y) { y }; (fn(x) {id(x)} : [A] (A) -> A)
> let id = fn (y) { y }; (fn (x) { id(x) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
