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

: [B <: int] (B) -> B <: [A <: int, C] (A) -> A
> ok

# FIXME: check Mitchell's distrib & other quantifier-pushing relations



# poly!
fn[A](x : A) { x }
> fn [A](x: A) { x }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
>   fn [A](x: A) : A { x }
> [A] (A) -> A

fn[A,B](id : [A](A) -> A, (x,y):(A, B)) { (id(y),id(x)) }
> fn [A, B](id: [A] (A) -> A, (x, y): (A, B)) { (id(y), id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.0, .0.1)) → (.0.1, .0.0)
>   fn [A, B](id: [A_2] (A_2) -> A_2, (x, y): (A, B)) : (B, A) { (id(y), id(x)) }
> [A, B] ([A_2] (A_2) -> A_2, (A, B)) -> (B, A)

fn(id : [A](A) -> A, (x,y)) { (id(y),id(x)) }
> fn (id: [A] (A) -> A, (x, y)) { (id(y), id(x)) }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0, (.0.1, .0.0)) → (.0.0, .0.1)
>   fn [A, B](id: [A_2] (A_2) -> A_2, (x, y): (B, A)) : (A, B) { (id(y), id(x)) }
> [A, B] ([A_2] (A_2) -> A_2, (B, A)) -> (A, B)

fn[A](x : A) { if x.cond {x} else {x} }
> fn [A](x: A) { if x.cond{x} else {x} }
> typechecking error: Failure("incompat")

fn[A <: {cond:bool}](x : A) { if x.cond {x} else {x} }
> fn [A <: {cond: bool}](x: A) { if x.cond{x} else {x} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool)]. (.0.0) → .0.0
>   fn [A <: {cond: bool}](x: A) : A { if x.cond{x} else {x} }
> [A <: {cond: bool}] (A) -> A

fn(f) { fn[A](x : A) { f(x) } }
> fn (f) { fn [A](x: A) { f(x) } }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((⊤) → .0.0) → ∀⁺ 0:[⊥,⊤]. (.0.0) → .1.0
>   fn [A](f: (any) -> A) : [A_2] (A_2) -> A { fn [A_2](x: A_2) : A { f(x) } }
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
>   (fn [B](x: B) : B { x } : [A] (A) -> A)
> [A] (A) -> A

(fn[B] (x) { (x : B) } : [A] (A) -> A)
> (fn [B](x) { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
>   (fn [B](x: B) : B { (x : B) } : [A] (A) -> A)
> [A] (A) -> A

(fn[B] (x) : B { (x : B) } : [A] (A) -> A)
> (fn [B](x) : B { (x : B) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
>   (fn [B](x: B) : B { (x : B) } : [A] (A) -> A)
> [A] (A) -> A

fn[B <: {foo:int}] (x) : B { x }
> fn [B <: {foo: int}](x) : B { x }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0
>   fn [B <: {foo: int}](x: B) : B { x }
> [B <: {foo: int}] (B) -> B

fn[B <: {foo:int}] (x) { (x : B) }
> fn [B <: {foo: int}](x) { (x : B) }
> * ⊢ ∀⁺ 0:[⊥,(foo: int)]. (.0.0) → .0.0
>   fn [B <: {foo: int}](x: B) : B { (x : B) }
> [B <: {foo: int}] (B) -> B

(fn() { @true } : [A]() -> bool)
> (fn () { @true } : [A] () -> bool)
> typechecking error: Failure("pragma: true")

fn[A,B](x:A, y:B) { if true { x } else { y } }
> fn [A, B](x: A, y: B) { if true{x} else {y} }
> File "src/check.ml", line 22, characters 2-8: Assertion failed
> Raised at Lang__Check.env_gen_var in file "src/check.ml", line 22, characters 2-34
> Called from Lang__Typedefs.map_free_typ in file "src/typedefs.ml", line 297, characters 25-56
> Called from Lang__Typedefs.map_head in file "src/typedefs.ml", line 207, characters 46-55
> Called from Lang__Typedefs.map_free_typ in file "src/typedefs.ml", line 298, characters 24-68
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 43, characters 15-43
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Check.elab_poly in file "src/check.ml", line 226, characters 14-59
> Called from Lang__Check.infer' in file "src/check.ml", line 352, characters 7-797
> Called from Lang__Check.infer in file "src/check.ml", line 308, characters 17-29
> Called from Lang__Check.elab_gen in file "src/check.ml", line 190, characters 29-36
> Called from Dune__exe__Test_runner.run_cmd in file "test/test_runner.ml", line 50, characters 12-62
> 

fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }
> fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2
>   fn [A, B, R, B <: R, A <: R](x: A, y: B) : R { if true{x} else {y} }
> [A, B, R, B <: R, A <: R] (A, B) -> R

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; ch
> let ch = fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }; ch
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤], 0 ≤ 2, 1 ≤ 2. (.0.0, .0.1) → .0.2
>   let ch : [A, B, R, B <: R, A <: R] (A, B) ->
>   R =
>   fn [A, B, R, B <: R, A <: R](x: A, y: B) : R { if true{x} else {y} };
>   ch
> [A, B, R, B <: R, A <: R] (A, B) -> R

let ch = fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } }; fn (a,b) { ch(a, b) }
> let ch = fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} }; fn (a, b) { ch(a, b) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0
>   let ch : [A, B, R, B <: R, A <: R] (A, B) ->
>   R =
>   fn [A, B, R, B <: R, A <: R](x: A, y: B) : R { if true{x} else {y} };
>   fn [A](a: A, b: A) : A { ch(a, b) }
> [A] (A, A) -> A

(fn[A,B,R, A<:R, B<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R, B <: R](x: A, y: B) : R { if true{x} else {y} } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0
>   (fn [A, B, R, B <: R, A <: R](x: A, y: B) : R { if true{x} else {y} } : [A] (A,
>   A) ->
>   A)
> [A] (A, A) -> A

(fn[A,B,R, A<:R](x : A, y : B) : R { if true { x } else { y } } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R](x: A, y: B) : R { if true{x} else {y} } : [A] (A, A) -> A)
> typechecking error: Failure("incompat")

(fn[A,B,R, A<:R](x : A, y : B) : R { x } : [A] (A, A) -> A)
> (fn [A, B, R, A <: R](x: A, y: B) : R { x } : [A] (A, A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0, .0.0) → .0.0
>   (fn [A, B, R, A <: R](x: A, y: B) : R { x } : [A] (A, A) -> A)
> [A] (A, A) -> A

# debugging

let wid = fn (id: [B]({foo:B}) -> B) { id({foo:5}) }; fn(f) { wid(fn(x){let () = f(x); x.foo}) }
> let wid = fn (id: [B] ({foo: B}) -> B) { id({foo: 5}) }; fn (f) { wid(fn (x) { let () = f(x); x.foo }) }
> File "src/typedefs.ml", line 522, characters 19-25: Assertion failed
> Raised at Lang__Typedefs.wf_styp_gen in file "src/typedefs.ml", line 522, characters 19-31
> Called from Stdlib__map.Make.iter in file "map.ml", line 296, characters 20-25
> Called from Lang__Type_simplification.remove_joins.canon_var in file "src/type_simplification.ml", line 65, characters 4-24
> Called from Lang__Typedefs.map_free_typ in file "src/typedefs.ml", line 297, characters 25-56
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 43, characters 15-43
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 40, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 51, characters 16-48
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 40, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 40, characters 11-40
> Called from Lang__Type_simplification.remove_joins in file "src/type_simplification.ml", line 98, characters 11-47
> Called from Lang__Check.elab_gen in file "src/check.ml", line 194, characters 15-66
> Re-raised at Lang__Check.elab_gen in file "src/check.ml", line 195, characters 120-127
> Called from Lang__Check.elab_poly in file "src/check.ml", line 217, characters 20-26
> Called from Lang__Check.infer' in file "src/check.ml", line 352, characters 7-797
> Called from Lang__Check.infer in file "src/check.ml", line 308, characters 17-29
> Called from Lang__Check.infer' in file "src/check.ml", line 346, characters 21-35
> Called from Lang__Check.infer in file "src/check.ml", line 308, characters 17-29
> Called from Lang__Check.elab_gen in file "src/check.ml", line 190, characters 29-36
> Called from Dune__exe__Test_runner.run_cmd in file "test/test_runner.ml", line 50, characters 12-62
> 

let wid = fn (id: [B,A <: {foo:B}](A) -> B) { id({foo:5}) }; fn(f) { wid(fn(x){let z = f({bar:x}); x.foo}) }
> let wid = fn (id: [B, A <: {foo: B}] (A) -> B) { id({foo: 5}) }; fn (f) { wid(fn (x) { let z = f({bar: x}); x.foo }) }
> File "src/typedefs.ml", line 522, characters 19-25: Assertion failed
> Raised at Lang__Typedefs.wf_styp_gen in file "src/typedefs.ml", line 522, characters 19-31
> Called from Stdlib__map.Make.iter in file "map.ml", line 296, characters 20-25
> Called from Lang__Type_simplification.remove_joins.canon_var in file "src/type_simplification.ml", line 65, characters 4-24
> Called from Lang__Typedefs.map_free_typ in file "src/typedefs.ml", line 297, characters 25-56
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 43, characters 15-43
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 40, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 51, characters 16-48
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 40, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 41, characters 11-40
> Called from Lang__Elab.map_free_elab_req in file "src/elab.ml", line 40, characters 11-40
> Called from Lang__Type_simplification.remove_joins in file "src/type_simplification.ml", line 98, characters 11-47
> Called from Lang__Check.elab_gen in file "src/check.ml", line 194, characters 15-66
> Re-raised at Lang__Check.elab_gen in file "src/check.ml", line 195, characters 120-127
> Called from Lang__Check.elab_poly in file "src/check.ml", line 217, characters 20-26
> Called from Lang__Check.infer' in file "src/check.ml", line 352, characters 7-797
> Called from Lang__Check.infer in file "src/check.ml", line 308, characters 17-29
> Called from Lang__Check.infer' in file "src/check.ml", line 346, characters 21-35
> Called from Lang__Check.infer in file "src/check.ml", line 308, characters 17-29
> Called from Lang__Check.elab_gen in file "src/check.ml", line 190, characters 29-36
> Called from Dune__exe__Test_runner.run_cmd in file "test/test_runner.ml", line 50, characters 12-62
> 

let id = fn(x) { x }; fn () { (id (id), id) }
> let id = fn (x) { x }; fn () { (id(id), id) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → ((.0.0) → .0.0, ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0)
>   let id : [A] (A) -> A = fn [A](x: A) : A { x };
>   fn [A]() : ((A) -> A, [B] (B) -> B) { (id(id), id) }
> [A] () -> ((A) -> A, [B] (B) -> B)


fn(f) { fn(id: [A] (A) -> A) { let x = f(id); id(1) } }
> fn (f) { fn (id: [A] (A) -> A) { let x = f(id); id(1) } }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. (((.0.1) → .0.1) → .0.0) → (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → int
>   fn [A, B](f: ((B) -> B) -> A) : ([A_2] (A_2) -> A_2) ->
>   int { fn (id: [A_2] (A_2) -> A_2) : int { let x : A = f(id); id(1) } }
> [A, B] (((B) -> B) -> A) -> ([A_2] (A_2) -> A_2) -> int

fn(f) { fn(id: [A] (A) -> A) { id(fn(y) { let x = f(y); y }) } }
> fn (f) { fn (id: [A] (A) -> A) { id(fn (y) { let x = f(y); y }) } }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((.0.1) → .0.0) → ∀⁺ 0:[⊥,.1.1]. (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → (
>   .0.0) → .0.0
>   fn [A, B](f: (B) -> A) : [C <: B] ([A_2] (A_2) -> A_2) ->
>   (C) ->
>   C {
>   fn [C <: B](id: [A_2] (A_2) -> A_2) : (C) ->
>   C { id(fn [D <: B](y: D) : D { let x : A = f(y); y }) }
>   }
> [A, B] ((B) -> A) -> [C <: B] ([A_2] (A_2) -> A_2) -> (C) -> C


(fn(x) {(fn(y){y})(x)} : [A] (A) -> A)
> (fn (x) { (fn (y) { y })(x) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
>   (fn [A](x: A) : A { (fn [B](y: B) : B { y })(x) } : [A] (A) -> A)
> [A] (A) -> A

let id = fn(y) { y }; (fn[A](x : A) {id(x)})
> let id = fn (y) { y }; (fn [A](x: A) { id(x) })
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
>   let id : [A] (A) -> A = fn [A](y: A) : A { y }; (fn [A](x: A) : A { id(x) })
> [A] (A) -> A

let id = fn(y) { y }; (fn(x) {id(x)} : [A] (A) -> A)
> let id = fn (y) { y }; (fn (x) { id(x) } : [A] (A) -> A)
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
>   let id : [A] (A) -> A = fn [A](y: A) : A { y };
>   (fn [A](x: A) : A { id(x) } : [A] (A) -> A)
> [A] (A) -> A


fn[A,B](x : [X, X :> A, X <: B](X) -> X) : (A) -> B { x }
> fn [A, B](x: [X, X :> A, X <: B] (X) -> X) : (A) -> B { x }
> typechecking error: Failure("incompat")

fn[A,B,A <: B](x : [X, X :> A, X <: B](X) -> X) : (A) -> B { x }
> fn [A, B, A <: B](x: [X, X :> A, X <: B] (X) -> X) : (A) -> B { x }
> *
> ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 0 ≤ 1. (∀⁻ 0:[.1.0,.1.1]. (.0.0) → .0.0) → (.0.0) → .0.1
>   fn [A, B, A <: B](x: [X <: B, X :> A] (X) -> X) : (A) -> B { x }
> [A, B, A <: B] ([X <: B, X :> A] (X) -> X) -> (A) -> B

fn[A,B,A <: B](x : [X, X <: A, X :> B](X) -> X) : [X <: A, Y :> B, X <: Y](X) -> Y { x }
> fn [A, B, A <: B](x: [X, X <: A, X :> B] (X) -> X) : [X <: A, Y :> B, X <: Y] (X) -> Y { x }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤],
> 0 ≤ 1. (∀⁻ 0:[.1.1,.1.0]. (.0.0) → .0.0) → ∀⁺ 0:[⊥,.1.0], 1:[.1.1,⊤],
> 0 ≤ 1. (.0.0) → .0.1
>   fn [A, B, A <: B](x: [X <: A, X :> B] (X) -> X) : [X <: A, Y :> B, X <: Y] (X) ->
>   Y { x }
> [A, B, A <: B] ([X <: A, X :> B] (X) -> X) -> [X <: A, Y :> B, X <: Y] (X) -> Y
