# FIXME: currently using internal syntax (Typedefs.pr_*)

#
# Literals
#

0
> * ⊢ int

5
> * ⊢ int

true
> * ⊢ bool

false
> * ⊢ bool

# FIXME: string syntax
# FIXME: interesting numeric literals (negative, hex, float, etc.)

# checking forms

(42 : int)
> * ⊢ int

(true : bool)
> * ⊢ bool

(42 : string)
> typechecking error: Failure("incompat")

#
# If
#

if (true) { 1 } else { 2 }
> * ⊢ int

if (false) { 1 } else { false }
> * ⊢ ⊤

#
# Tuples
#

(1, 2)
> * ⊢ (int, int)

(true, 3, 4)
> * ⊢ (bool, int, int)

# python-style singleton tuples
(4,)
> * ⊢ (int)

{foo:1}
> * ⊢ (foo: int)

# not a singleton tuple
(1)
> * ⊢ int

# arity
((1,),(2,3),(4,5,6),(7,8,9,10))
> * ⊢ ((int), (int, int), (int, int, int), (int, int, int, int))

# empty tuple (unit type)
()
> * ⊢ ()

# named fields
({foo:20, bar:17}, {baz:1})
> * ⊢ ((foo: int, bar: int), (baz: int))

# FIXME mixture of named and unnamed
# (1, 2, .bar=3, .baz=true)
# > * ⊢ (int, int, bar: int, baz: bool)

# joins
if (true) { (1, 2) } else { (1, true, 3) }
> * ⊢ (int, ⊤, ...)

if (false) { {foo:1,bar:2} } else { {foo:1,baz:()} }
> * ⊢ (foo: int, ...)

true.foo
> typechecking error: Failure("incompat")

@bot
> * ⊢ ⊥

# checking join of functions and meet of records
if true { (@bot : (~foo:(int,int), ~bar:any) -> string) } else { (@bot : (~foo:(int,int), ~bar:any) -> string) }
> * ⊢ (foo: (int, int), bar: ⊤) → string

if true { (@bot : ((int,any), ~foo:(int,int), ~bar:any) -> string) } else {(@bot : ((any,string), ~bar:string, ~foo:(string,any)) -> nothing)}
> * ⊢ ((int, string), foo: (⊥, int), bar: string) → string



#
# Bidirectional typing. @true and @false have only checking forms.
#

@true
> typechecking error: Failure("pragma: true")

(@true : bool)
> * ⊢ bool

((@true, @false) : (bool, bool))
> * ⊢ (bool, bool)

((1, 2) : (int, int, int))
> typechecking error: Failure("missing pos")

((1, 2, 3) : (int, int))
> typechecking error: Failure("extra")

# weird. Should I allow this? eta-expansion?
# (1, 2, ...)
# > * ⊢ (int, int, ...)

((1, 2) : (int, int, ...))
> * ⊢ (int, int, ...)

# FIXME: should this be allowed?
# ((1, 2, 3) : (int, int, ...))


# A checking form for projections! Isn't subtyping great?
({foo: @true}.foo : bool)
> * ⊢ bool

#
# Let-bindings and patterns
#

let x = 1; x
> * ⊢ int

(let x = @true; x : bool)
> typechecking error: Failure("pragma: true")

(let x : bool = @true; (x, @false) : (bool,bool))
> * ⊢ (bool, bool)

let x = (1, 2); x
> * ⊢ (int, int)

let x : int = (1, 2); x
> typechecking error: Failure("incompat")

let x : bool = true; x
> * ⊢ bool

let x : bool = 5; x
> typechecking error: Failure("incompat")

let {x: foo, y: bar} = {x: 10, y: true}; (foo, bar)
> * ⊢ (int, bool)

let {x: foo, y: bar} = {x: 10, y: true, z: 42}; (foo, bar)
> typechecking error: Failure("extra")

let {x: foo, y: bar, ...} = {x: 10, y: true, z: 42}; (foo, bar)
> * ⊢ (int, bool)


# Tuple bindings

let (x, y) = (1, true); (y, x)
> * ⊢ (bool, int)

let (x, y, ...) = (false, (), 3); {x,y}
> * ⊢ (x: bool, y: ())


let {x: foo, y: bar} : {x:int, y:bool} = {x:1, y:true}; foo
> * ⊢ int
let {x: foo, y: bar} : {x:int} = {x:1, y:true}; foo
> typechecking error: Failure("extra")
let {x: foo, y: bar} : {x:int,y:int} = {x:1, y:true}; foo
> typechecking error: Failure("incompat")
let {x: foo, y: bar} : {x:int,y:bool,z:bool} = {x:1, y:true}; foo
> typechecking error: Failure("missing z")

# punning

let {x, y} : {x:int, y:bool} = {x:1, y:true}; (y,x)
> * ⊢ (bool, int)

let {x, y} = {x:1, y:true}; (y,x)
> * ⊢ (bool, int)

let {x, y} = {x:1, y:true}; {y,x,z:3}
> * ⊢ (y: bool, x: int, z: int)

let {x, y} = {x:1, y:true}; ({y,x,z:3} : {y: bool, x: int, z: int})
> * ⊢ (y: bool, x: int, z: int)


# subtyping checks. FIXME: these probably only hit matching :(
let a = {foo: 1, bar: 2}; let b : {foo: int, bar: int} = a; b
> * ⊢ (foo: int, bar: int)

let a = {foo: 1, bar: 2}; let b : {bar: int} = a; b
> typechecking error: Failure("extra")

let a = {foo: 1, bar: 2}; let b : {bar: any, ...} = a; b
> * ⊢ (bar: ⊤, ...)

let a = {foo: 1, bar: 2}; let b : {bar: nothing, ...} = a; b
> typechecking error: Failure("incompat")

# function types
fn (f: (int,int) -> int) { f(1,2) }
> * ⊢ ((int, int) → int) → int

fn (f: (~x:int,~y:int) -> int) { f(~x:1, ~y:2) }
> * ⊢ ((x: int, y: int) → int) → int

fn (f: (~x:int,~y:int) -> int) { let x = 1; f(~x, ~y:2) }
> * ⊢ ((x: int, y: int) → int) → int

fn () { (fn (~x, ~y) { {x,y} }) (~y:1, ~x:()) }
> * ⊢ () → (x: (), y: int)

#
# Lambda
#

fn (a, b) { (b, a.foo) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((foo: .0.1, ...), .0.0) → (.0.0, .0.1)

fn (a, b) : int { b }
> * ⊢ (⊤, int) → int

fn (a : int, b) : (int, int) { (a, b) }
> * ⊢ (int, int) → (int, int)

(fn (a) { (a, @true) } : (int) -> (int, bool))
> * ⊢ (int) → (int, bool)

fn (a) { if (a.foo) { {bar: a.bar} } else { a } }
> *
> ⊢
> ∀⁺ 0:[⊥,(foo: bool, bar: .0.1, ...)], 1:[⊥,⊤], 2:[(bar: .0.1),⊤],
> 0 ≤ 2. (.0.0) → .0.2

(fn (a) { a })(5)
> *0: [int, ⊤],  ⊢ #0.0

# tricky: the second 5 should be checked against Top (i.e. inferred)
(fn (a,b) { a })(5,5)
> *0: [int, ⊤],  ⊢ #0.0
(fn (a,b) { a })(5,if 5 { 5 } else { 5 })
> typechecking error: Failure("incompat")


fn(b) { (fn (a) { if (a.cond) { a } else { a } })(if true { b } else { {foo: 1, cond: false} }) }
> * ⊢ ∀⁺ 0:[(foo: int, cond: bool),(cond: bool, ...)]. (.0.0) → .0.0

fn(b) { if (b.cond) { b } else { {foo: 1, cond: false} } }
> *
> ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[(foo: int, cond: bool),⊤], 0 ≤ 1. (.0.0) → .0.1

fn(b) { if (b.cond) { b } else { {foo: 1, cond: 4} } }
> *
> ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[(foo: int, cond: int),⊤], 0 ≤ 1. (.0.0) → .0.1

fn (x) { (x.foo, x.bar, x.foo) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((foo: .0.0, bar: .0.1, ...)) → (.0.0, .0.1, .0.0)

fn (x) { if (x.cond) { (x.foo, x.bar) } else { (x.foo, x.foo) } }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤],
> 0 ≤ 1. ((cond: bool, foo: .0.0, bar: .0.1, ...)) → (.0.0, .0.1)

fn (x) { ((fn(x){x.foo})(x), (fn(x){x.foo})(x))  }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((foo: .0.0, ...)) → (.0.0, .0.0)

# nested constraints, garbage variables
fn (x) { (fn(y) { y.foo.bar })({foo:{bar:x}}) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0

# Trying to make an example with meets/joins under ctors in bounds
fn (x, f, g) { ( f(x.foo), g(x.foo) ) }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤]. ((foo: .0.2, ...), (.0.2) → .0.0, (.0.2) → .0.1) → (
>   .0.0,
>   .0.1)

# same example in garbage position
(fn(x) { 5 }) (fn (x, f, g) { ( f(x.foo), g(x.foo) ) })
> * ⊢ int

# garbage
fn (x) { (fn (y) { 5 })(if (x.cond) { (x.a, x.b) } else { (x.b, x.a) }) }
> * ⊢ ((cond: bool, a: ⊤, b: ⊤, ...)) → int


fn (x) { if (x.cond) { (x.a, x.b) } else { (x.b, x.a) } }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((cond: bool, a: .0.0, b: .0.0, ...)) → (.0.0, .0.0)

fn (x) { if (x.cond) { (x, 5) } else { (x, x) } }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[int,⊤], 0 ≤ 1. (.0.0) → (.0.0, .0.1)

fn (x) { if (x.cond) { (x, 5) } else { (x, x.n) } }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool, n: .0.1, ...)], 1:[int,⊤]. (.0.0) → (.0.0, .0.1)

# once
# this is a very disappointing type. The α/γ pair needs to go!
fn (f, x) { f(x) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((.0.1) → .0.0, .0.1) → .0.0

# twice!
fn (f, x) { f(f(x)) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 0 ≤ 1. ((.0.1) → .0.0, .0.1) → .0.0

# can I hit approx with nested lambda-generalisations? trickier than I thought.
fn (f) { fn(x) { (f(x), x) } }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((.0.1) → .0.0) → ∀⁺ 0:[⊥,.1.1]. (.0.0) → (.1.0, .0.0)


# poly id as an argument!
fn (f) { (f(1), f(true)) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((⊤) → .0.0) → (.0.0, .0.0)

fn (f : [A] (A) -> A) { (f(1), f(true)) }
> * ⊢ (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → (int, bool)

fn (x, wid : (([A] (A) -> A) -> int)) { wid(fn(a){{x:x(a),y:a}.y}) }
> * ⊢ (⊤, (∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0) → int) → int

fn (x, wid : (([A <: {foo:int}, A :> {foo:int,bar:string}] (A) -> A) -> int)) { wid(fn(a){x(a)}) }
> *
> ⊢
> (
>   ((foo: int)) → (foo: int, bar: string),
>   (∀⁺ 0:[(foo: int, bar: string),(foo: int)]. (.0.0) → .0.0) → int) → int

fn(f) { (fn(x) { 5 })(f(10)) }
> * ⊢ ((int) → ⊤) → int


# needs approx
(fn (x) { x })(fn (x) { x })
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
> Called from Dune__exe__Test_runner.run_cmd in file "test/test_runner.ml", line 39, characters 12-36
> 

# self-app
(fn (x) { x(x) }) (fn (x) { x(x) })
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
> Called from Dune__exe__Test_runner.run_cmd in file "test/test_runner.ml", line 39, characters 12-36
> 
