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
> [A] (A) -> A

fn[A,B](id : [A](A) -> A, (x,y):(A, B)) { (id(y),id(x)) }
> fn [A, B](id: [A] (A) -> A, (x, y): (A, B)) { (id(y), id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.0, .0.1)) → (.0.1, .0.0)
> [A, B] ([A_2] (A_2) -> A_2, (A, B)) -> (B, A)

fn(id : [A](A) -> A, (x,y)) { (id(y),id(x)) }
> fn (id: [A] (A) -> A, (x, y)) { (id(y), id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.1, .0.0)) → (.0.0, .0.1)
> [A, B] ([A_2] (A_2) -> A_2, (B, A)) -> (A, B)

fn[A](x : A) { if x.cond {x} else {x} }
> fn [A](x: A) { if x.cond{x} else {x} }
> typechecking error: Failure("incompat")

fn[A <: {cond:bool}](x : A) { if x.cond {x} else {x} }
> fn [A <: {cond: bool}](x: A) { if x.cond{x} else {x} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool)]. (.0.0) → .0.0
> [A <: {cond: bool}] (A) -> A

fn(f) { fn[A](x : A) { f(x) } }
> fn (f) { fn [A](x: A) { f(x) } }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((⊤) → .0.0) → ∀⁺ 0:[⊥,⊤]. (.0.0) → .1.0
> [A] ((any) -> A) -> [A_2] (A_2) -> A

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
> [A] (A) -> A

(fn[B] (x) { (x : B) } : [A] (A) -> A)
> (fn [B](x) { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
> [A] (A) -> A

(fn[B] (x) : B { (x : B) } : [A] (A) -> A)
> (fn [B](x) : B { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
> [A] (A) -> A

fn[B <: {foo:int}] (x) : B { x }
> fn [B <: {foo: int}](x) : B { x }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0
> [B <: {foo: int}] (B) -> B

fn[B <: {foo:int}] (x) { (x : B) }
> fn [B <: {foo: int}](x) { (x : B) }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0
> [B <: {foo: int}] (B) -> B

(fn() { @true } : [A]() -> bool)
> (fn () { @true } : [A] () -> bool)
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → bool
> [A] () -> bool

fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }
> fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2
> [A, B, R, B <: R, A <: R] (A, B) -> R

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; ch
> let ch = fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }; ch
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2
> [A, B, R, B <: R, A <: R] (A, B) -> R

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; fn (a,b) { ch(a, b) }
> let ch = fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }; fn (a, b) { ch(a, b) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0
> [A] (A, A) -> A

(fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0
> [A] (A, A) -> A

(fn[A,B,R, A<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R](x: A, y: B) : R { if true{x} else {y} } : [A] (A, A) -> A)
> typechecking error: Failure("incompat")

(fn[A,B,R, A<:R](x : A, y : B) : R { x } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R](x: A, y: B) : R { x } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0
> [A] (A, A) -> A

let wid = fn (id: [B,A <: {foo:B}](A) -> B) { id({foo:5}) }; fn(f) { wid(fn(x){let z = f({bar:x}); x.foo}) }
> let wid = fn (id: [B, A <: {foo: B}] (A) -> B) { id({foo: 5}) }; fn (f) { wid(fn (x) { let z = f({bar: x}); x.foo }) }
> * ⊢ (((bar: (foo: ⊤))) → ⊤) → int
> (({bar: {foo: any}}) -> any) -> int

let id = fn(x) { x }; fn () { (id (id), id) }
> let id = fn (x) { x }; fn () { (id(id), id) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → ((.0.0) → .0.0, ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0)
> [A] () -> ((A) -> A, [B] (B) -> B)


fn(f) { fn(id: [A] (A) -> A) { let x = f(id); id(1) } }
> fn (f) { fn (id: [A] (A) -> A) { let x = f(id); id(1) } }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (((.0.0) → .0.0) → ⊤) → (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → int
> [A] (((A) -> A) -> any) -> ([A_2] (A_2) -> A_2) -> int

fn(f) { fn(id: [A] (A) -> A) { id(fn(y) { let x = f(y); y }) } }
> fn (f) { fn (id: [A] (A) -> A) { id(fn (y) { let x = f(y); y }) } }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤]. ((.0.0) → ⊤) → ∀⁺ 0:[⊥,.1.0]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → (.0.0) → .0.0
> [A] ((A) -> any) -> [B <: A] ([A_2] (A_2) -> A_2) -> (B) -> B


(fn(x) {(fn(y){y})(x)} : [A] (A) -> A)
> (fn (x) { (fn (y) { y })(x) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
> [A] (A) -> A

let id = fn(y) { y }; (fn[A](x : A) {id(x)})
> let id = fn (y) { y }; (fn [A](x: A) { id(x) })
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
> [A] (A) -> A

let id = fn(y) { y }; (fn(x) {id(x)} : [A] (A) -> A)
> let id = fn (y) { y }; (fn (x) { id(x) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
> [A] (A) -> A


fn[A,B](x : [X, X :> A, X <: B](X) -> X) : (A) -> B { x }
> fn [A, B](x: [X, X :> A, X <: B] (X) -> X) : (A) -> B { x }
> typechecking error: Failure("incompat")

fn[A,B,A <: B](x : [X, X :> A, X <: B](X) -> X) : (A) -> B { x }
> fn [A, B, A <: B](x: [X, X :> A, X <: B] (X) -> X) : (A) -> B { x }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 0 ≤ 1. (∀⁻ 0:[.1.0,.1.1]. (.0.0) → .0.0) → (.0.0) → .0.1
> [A, B, A <: B] ([X <: B, X :> A] (X) -> X) -> (A) -> B

fn[A,B,A <: B](x : [X, X <: A, X :> B](X) -> X) : [X <: A, Y :> B, X <: Y](X) -> Y { x }
> fn [A, B, A <: B](x: [X, X <: A, X :> B] (X) -> X) : [X <: A, Y :> B, X <: Y] (X) -> Y { x }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤],
> 0 ≤ 1. (∀⁻ 0:[.1.1,.1.0]. (.0.0) → .0.0) → ∀⁺ 0:[⊥,.1.0], 1:[.1.1,⊤],
> 0 ≤ 1. (.0.0) → .0.1
> [A, B, A <: B] ([X <: A, X :> B] (X) -> X) -> [X <: A, Y :> B, X <: Y] (X) -> Y
