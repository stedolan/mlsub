# FIXME: currently using internal syntax (Typedefs.pr_*)

#
# Literals
#

0
> 0
> * ⊢ int
> int

5
> 5
> * ⊢ int
> int

true
> true
> * ⊢ bool
> bool

false
> false
> * ⊢ bool
> bool

# FIXME: string syntax
# FIXME: interesting numeric literals (negative, hex, float, etc.)

# checking forms

(42 : int)
> (42 : int)
> * ⊢ int
> int

(true : bool)
> (true : bool)
> * ⊢ bool
> bool

(42 : string)
> (42 : string)
> typechecking error: Failure("incompat")

#
# If
#

if (true) { 1 } else { 2 }
> if (true){1} else {2}
> * ⊢ int
> int

if (false) { 1 } else { false }
> if (false){1} else {false}
> * ⊢ ⊤
> any

#
# Tuples
#

(1, 2)
> (1, 2)
> * ⊢ (int, int)
> (int, int)

(true, 3, 4)
> (true, 3, 4)
> * ⊢ (bool, int, int)
> (bool, int, int)

# python-style singleton tuples
(4,)
> (4,)
> * ⊢ (int)
> (int,)

{foo:1}
> {foo: 1}
> * ⊢ (foo: int)
> {foo: int}

# not a singleton tuple
(1)
> (1)
> * ⊢ int
> int

# arity
((1,),(2,3),(4,5,6),(7,8,9,10))
> ((1,), (2, 3), (4, 5, 6), (7, 8, 9, 10))
> * ⊢ ((int), (int, int), (int, int, int), (int, int, int, int))
> ((int,), (int, int), (int, int, int), (int, int, int, int))

# empty tuple (unit type)
()
> ()
> * ⊢ ()
> ()

# trailing comma in types, too
((1,) : (int,))
> ((1,) : (int,))
> * ⊢ (int)
> (int,)

((1,) : (int))
> ((1,) : (int))
> typechecking error: Failure("incompat")

# and patterns
let (x,) = (1,); {x}
> let (x,) = (1,); {x}
> * ⊢ (x: int)
> {x: int}

let (x) = (1,); {x}
> let (x) = (1,); {x}
> * ⊢ (x: (int))
> {x: (int,)}

# named fields
({foo:20, bar:17}, {baz:1})
> ({foo: 20, bar: 17}, {baz: 1})
> * ⊢ ((foo: int, bar: int), (baz: int))
> ({foo: int, bar: int}, {baz: int})

# FIXME mixture of named and unnamed
# (1, 2, .bar=3, .baz=true)
# > * ⊢ (int, int, bar: int, baz: bool)

# joins
if (true) { (1, 2) } else { (1, true, 3) }
> if (true){(1, 2)} else {(1, true, 3)}
> * ⊢ (int, ⊤, ...)
> (int, any, ...)

if (false) { {foo:1,bar:2} } else { {foo:1,baz:()} }
> if (false){{foo: 1, bar: 2}} else {{foo: 1, baz: ()}}
> * ⊢ (foo: int, ...)
> {foo: int, ...}

true.foo
> true.foo
> typechecking error: Failure("incompat")

@bot
> @bot
> * ⊢ ⊥
> nothing

# checking join of functions and meet of records
if true { (@bot : (~foo:(int,int), ~bar:any) -> string) } else { (@bot : (~foo:(int,int), ~bar:any) -> string) }
> if true{(@bot : (~foo: (int, int), ~bar: any) -> string)} else {(@bot : (~foo: (int, int), ~bar: any) -> string)}
> * ⊢ (foo: (int, int), bar: ⊤) → string
> (~foo: (int, int), ~bar: any) -> string

if true { (@bot : ((int,any), ~foo:(int,int), ~bar:any) -> string) } else {(@bot : ((any,string), ~bar:string, ~foo:(string,any)) -> nothing)}
> if
> true{(@bot : ((int, any), ~foo: (int, int), ~bar: any) -> string)} else
> {(@bot : ((any, string), ~bar: string, ~foo: (string, any)) -> nothing)}
> * ⊢ ((int, string), foo: (⊥, int), bar: string) → string
> ((int, string), ~foo: (nothing, int), ~bar: string) -> string


#
# Bidirectional typing. @true and @false have only checking forms.
#

@true
> @true
> typechecking error: Failure("pragma: true")

(@true : bool)
> (@true : bool)
> * ⊢ bool
> bool

((@true, @false) : (bool, bool))
> ((@true, @false) : (bool, bool))
> * ⊢ (bool, bool)
> (bool, bool)

((1, 2) : (int, int, int))
> ((1, 2) : (int, int, int))
> typechecking error: Failure("missing .2")

((1, 2, 3) : (int, int))
> ((1, 2, 3) : (int, int))
> typechecking error: Failure("extra")

# weird. Should I allow this? eta-expansion?
# (1, 2, ...)
# > * ⊢ (int, int, ...)

((1, 2) : (int, int, ...))
> ((1, 2) : (int, int, ...))
> * ⊢ (int, int, ...)
> (int, int, ...)

((1, 2, 3) : (int, int, ...))
> ((1, 2, 3) : (int, int, ...))
> * ⊢ (int, int, ...)
> (int, int, ...)


# A checking form for projections! Isn't subtyping great?
({foo: @true}.foo : bool)
> ({foo: @true}.foo : bool)
> * ⊢ bool
> bool

# Generalisation of functions allows checking against inferred argument types
(fn(x) { if x.cond { 1 } else { 2 }})({cond: @true})
> (fn (x) { if x.cond{1} else {2} })({cond: @true})
> * ⊢ int
> int

#
# Let-bindings and patterns
#

let x = 1; x
> let x = 1; x
> * ⊢ int
> int

(let x = @true; x : bool)
> (let x = @true; x : bool)
> typechecking error: Failure("pragma: true")

(let x : bool = @true; (x, @false) : (bool,bool))
> (let x : bool = @true; (x, @false) : (bool, bool))
> * ⊢ (bool, bool)
> (bool, bool)

let x = (1, 2); x
> let x = (1, 2); x
> * ⊢ (int, int)
> (int, int)

let x : int = (1, 2); x
> let x : int = (1, 2); x
> typechecking error: Failure("incompat")

let x : bool = true; x
> let x : bool = true; x
> * ⊢ bool
> bool

let x : bool = 5; x
> let x : bool = 5; x
> typechecking error: Failure("incompat")

let {x: foo, y: bar} = {x: 10, y: true}; (foo, bar)
> let {x: foo, y: bar} = {x: 10, y: true}; (foo, bar)
> * ⊢ (int, bool)
> (int, bool)

let {x: foo, y: bar} = {x: 10, y: true, z: 42}; (foo, bar)
> let {x: foo, y: bar} = {x: 10, y: true, z: 42}; (foo, bar)
> typechecking error: Failure("extra")

let {x: foo, y: bar, ...} = {x: 10, y: true, z: 42}; (foo, bar)
> let {x: foo, y: bar, ...} = {x: 10, y: true, z: 42}; (foo, bar)
> * ⊢ (int, bool)
> (int, bool)


# Tuple bindings

let (x, y) = (1, true); (y, x)
> let (x, y) = (1, true); (y, x)
> * ⊢ (bool, int)
> (bool, int)

let (x, y, ...) = (false, (), 3); {x,y}
> let (x, y, ...) = (false, (), 3); {x, y}
> * ⊢ (x: bool, y: ())
> {x: bool, y: ()}


let {x: foo, y: bar} : {x:int, y:bool} = {x:1, y:true}; foo
> let {x: foo, y: bar} : {x: int, y: bool} = {x: 1, y: true}; foo
> * ⊢ int
> int
let {x: foo, y: bar} : {x:int} = {x:1, y:true}; foo
> let {x: foo, y: bar} : {x: int} = {x: 1, y: true}; foo
> typechecking error: Failure("extra")
let {x: foo, y: bar} : {x:int,y:int} = {x:1, y:true}; foo
> let {x: foo, y: bar} : {x: int, y: int} = {x: 1, y: true}; foo
> typechecking error: Failure("incompat")
let {x: foo, y: bar} : {x:int,y:bool,z:bool} = {x:1, y:true}; foo
> let {x: foo, y: bar} : {x: int, y: bool, z: bool} = {x: 1, y: true}; foo
> typechecking error: Failure("missing z")

# punning

let {x, y} : {x:int, y:bool} = {x:1, y:true}; (y,x)
> let {x, y} : {x: int, y: bool} = {x: 1, y: true}; (y, x)
> * ⊢ (bool, int)
> (bool, int)

let {x, y} = {x:1, y:true}; (y,x)
> let {x, y} = {x: 1, y: true}; (y, x)
> * ⊢ (bool, int)
> (bool, int)

let {x, y} = {x:1, y:true}; {y,x,z:3}
> let {x, y} = {x: 1, y: true}; {y, x, z: 3}
> * ⊢ (y: bool, x: int, z: int)
> {y: bool, x: int, z: int}

let {x, y} = {x:1, y:true}; ({y,x,z:3} : {y: bool, x: int, z: int})
> let {x, y} = {x: 1, y: true}; ({y, x, z: 3} : {y: bool, x: int, z: int})
> * ⊢ (y: bool, x: int, z: int)
> {y: bool, x: int, z: int}


# subtyping checks. FIXME: these probably only hit matching :(
let a = {foo: 1, bar: 2}; let b : {foo: int, bar: int} = a; b
> let a = {foo: 1, bar: 2}; let b : {foo: int, bar: int} = a; b
> * ⊢ (foo: int, bar: int)
> {foo: int, bar: int}

let a = {foo: 1, bar: 2}; let b : {bar: int} = a; b
> let a = {foo: 1, bar: 2}; let b : {bar: int} = a; b
> typechecking error: Failure("extra")

let a = {foo: 1, bar: 2}; let b : {bar: any, ...} = a; b
> let a = {foo: 1, bar: 2}; let b : {bar: any, ...} = a; b
> * ⊢ (bar: ⊤, ...)
> {bar: any, ...}

let a = {foo: 1, bar: 2}; let b : {bar: nothing, ...} = a; b
> let a = {foo: 1, bar: 2}; let b : {bar: nothing, ...} = a; b
> typechecking error: Failure("incompat")

# function types
fn (f: (int,int) -> int) { f(1,2) }
> fn (f: (int, int) -> int) { f(1, 2) }
> * ⊢ ((int, int) → int) → int
> ((int, int) -> int) -> int

fn (f: (~x:int,~y:int) -> int) { f(~x:1, ~y:2) }
> fn (f: (~x: int, ~y: int) -> int) { f(~x: 1, ~y: 2) }
> * ⊢ ((x: int, y: int) → int) → int
> ((~x: int, ~y: int) -> int) -> int

fn (f: (~x:int,~y:int) -> int) { let x = 1; f(~x, ~y:2) }
> fn (f: (~x: int, ~y: int) -> int) { let x = 1; f(~x, ~y: 2) }
> * ⊢ ((x: int, y: int) → int) → int
> ((~x: int, ~y: int) -> int) -> int

fn () { (fn (~x, ~y) { {x,y} }) (~y:1, ~x:()) }
> fn () { (fn (~x, ~y) { {x, y} })(~y: 1, ~x: ()) }
> * ⊢ () → (x: (), y: int)
> () -> {x: (), y: int}

#
# Lambda
#

fn (a, b) { (b, a.foo) }
> fn (a, b) { (b, a.foo) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((foo: .0.1, ...), .0.0) → (.0.0, .0.1)
> [A, B] ({foo: B, ...}, A) -> (A, B)

fn (a, b) : int { b }
> fn (a, b) : int { b }
> * ⊢ (⊤, int) → int
> (any, int) -> int

fn (a : int, b) : (int, int) { (a, b) }
> fn (a: int, b) : (int, int) { (a, b) }
> * ⊢ (int, int) → (int, int)
> (int, int) -> (int, int)

(fn (a) { (a, @true) } : (int) -> (int, bool))
> (fn (a) { (a, @true) } : (int) -> (int, bool))
> * ⊢ (int) → (int, bool)
> (int) -> (int, bool)

fn (a) { if (a.foo) { {bar: a.bar} } else { a } }
> fn (a) { if (a.foo){{bar: a.bar}} else {a} }
> *
> ⊢
> ∀⁺ 0:[⊥,(foo: bool, bar: .0.1, ...)], 1:[⊥,⊤], 2:[(bar: .0.1),⊤],
> 0 ≤ 2. (.0.0) → .0.2
> [A <: {foo: bool, bar: B, ...}, B, C :> {bar: B}, A <: C] (A) -> C

(fn (a) { a })(5)
> (fn (a) { a })(5)
> *, 0: [int, ⊤],  ⊢ #1.0
> int

# tricky: the second 5 should be checked against Top (i.e. inferred)
(fn (a,b) { a })(5,5)
> (fn (a, b) { a })(5, 5)
> *, 0: [int, ⊤],  ⊢ #1.0
> int
(fn (a,b) { a })(5,if 5 { 5 } else { 5 })
> (fn (a, b) { a })(5, if 5{5} else {5})
> typechecking error: Failure("incompat")


fn(b) { (fn (a) { if (a.cond) { a } else { a } })(if true { b } else { {foo: 1, cond: false} }) }
> fn (b) { (fn (a) { if (a.cond){a} else {a} })(if true{b} else {{foo: 1, cond: false}}) }
> * ⊢ ∀⁺ 0:[(foo: int, cond: bool),(cond: bool, ...)]. (.0.0) → .0.0
> [A <: {cond: bool, ...}, A :> {foo: int, cond: bool}] (A) -> A

fn(b) { if (b.cond) { b } else { {foo: 1, cond: false} } }
> fn (b) { if (b.cond){b} else {{foo: 1, cond: false}} }
> *
> ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[(foo: int, cond: bool),⊤], 0 ≤ 1. (.0.0) → .0.1
> [A <: {cond: bool, ...}, B :> {foo: int, cond: bool}, A <: B] (A) -> B

fn(b) { if (b.cond) { b } else { {foo: 1, cond: 4} } }
> fn (b) { if (b.cond){b} else {{foo: 1, cond: 4}} }
> *
> ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[(foo: int, cond: int),⊤], 0 ≤ 1. (.0.0) → .0.1
> [A <: {cond: bool, ...}, B :> {foo: int, cond: int}, A <: B] (A) -> B

fn (x) { (x.foo, x.bar, x.foo) }
> fn (x) { (x.foo, x.bar, x.foo) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((foo: .0.0, bar: .0.1, ...)) → (.0.0, .0.1, .0.0)
> [A, B] ({foo: A, bar: B, ...}) -> (A, B, A)

fn (x) { if (x.cond) { (x.foo, x.bar) } else { (x.foo, x.foo) } }
> fn (x) { if (x.cond){(x.foo, x.bar)} else {(x.foo, x.foo)} }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤],
> 0 ≤ 1. ((cond: bool, foo: .0.0, bar: .0.1, ...)) → (.0.0, .0.1)
> [A, B, A <: B] ({cond: bool, foo: A, bar: B, ...}) -> (A, B)

fn (x) { ((fn(x){x.foo})(x), (fn(x){x.foo})(x))  }
> fn (x) { ((fn (x) { x.foo })(x), (fn (x) { x.foo })(x)) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((foo: .0.0, ...)) → (.0.0, .0.0)
> [A] ({foo: A, ...}) -> (A, A)

# nested constraints, garbage variables
fn (x) { (fn(y) { y.foo.bar })({foo:{bar:x}}) }
> fn (x) { (fn (y) { y.foo.bar })({foo: {bar: x}}) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
> [A] (A) -> A

# Trying to make an example with meets/joins under ctors in bounds
fn (x, f, g) { ( f(x.foo), g(x.foo) ) }
> fn (x, f, g) { (f(x.foo), g(x.foo)) }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤]. ((foo: .0.2, ...), (.0.2) → .0.0, (.0.2) → .0.1) → (
>   .0.0,
>   .0.1)
> [A, B, C] ({foo: C, ...}, (C) -> A, (C) -> B) -> (A, B)

# same example in garbage position
(fn(x) { 5 }) (fn (x, f, g) { ( f(x.foo), g(x.foo) ) })
> (fn (x) { 5 })(fn (x, f, g) { (f(x.foo), g(x.foo)) })
> * ⊢ int
> int

# garbage
fn (x) { (fn (y) { 5 })(if (x.cond) { (x.a, x.b) } else { (x.b, x.a) }) }
> fn (x) { (fn (y) { 5 })(if (x.cond){(x.a, x.b)} else {(x.b, x.a)}) }
> * ⊢ ((cond: bool, a: ⊤, b: ⊤, ...)) → int
> ({cond: bool, a: any, b: any, ...}) -> int


fn (x) { if (x.cond) { (x.a, x.b) } else { (x.b, x.a) } }
> fn (x) { if (x.cond){(x.a, x.b)} else {(x.b, x.a)} }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((cond: bool, a: .0.0, b: .0.0, ...)) → (.0.0, .0.0)
> [A] ({cond: bool, a: A, b: A, ...}) -> (A, A)

fn (x) { if (x.cond) { (x, 5) } else { (x, x) } }
> fn (x) { if (x.cond){(x, 5)} else {(x, x)} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[int,⊤], 0 ≤ 1. (.0.0) → (.0.0, .0.1)
> [A <: {cond: bool, ...}, B :> int, A <: B] (A) -> (A, B)

fn (x) { if (x.cond) { (x, 5) } else { (x, x.n) } }
> fn (x) { if (x.cond){(x, 5)} else {(x, x.n)} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool, n: .0.1, ...)], 1:[int,⊤]. (.0.0) → (.0.0, .0.1)
> [A <: {cond: bool, n: B, ...}, B :> int] (A) -> (A, B)

# once
# this is a very disappointing type. The α/γ pair needs to go!
fn (f, x) { f(x) }
> fn (f, x) { f(x) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((.0.1) → .0.0, .0.1) → .0.0
> [A, B] ((B) -> A, B) -> A

# twice!
fn (f, x) { f(f(x)) }
> fn (f, x) { f(f(x)) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 0 ≤ 1. ((.0.1) → .0.0, .0.1) → .0.0
> [A, B, A <: B] ((B) -> A, B) -> A

# can I hit approx with nested lambda-generalisations? trickier than I thought.
fn (f) { fn(x) { (f(x), x) } }
> fn (f) { fn (x) { (f(x), x) } }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((.0.1) → .0.0) → ∀⁺ 0:[⊥,.1.1]. (.0.0) → (.1.0, .0.0)
> [A, B] ((B) -> A) -> [C <: B] (C) -> (A, C)


# poly id as an argument!
fn (f) { (f(1), f(true)) }
> fn (f) { (f(1), f(true)) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((⊤) → .0.0) → (.0.0, .0.0)
> [A] ((any) -> A) -> (A, A)

fn (f : [A] (A) -> A) { (f(1), f(true)) }
> fn (f: [A] (A) -> A) { (f(1), f(true)) }
> * ⊢ (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → (int, bool)
> ([A] (A) -> A) -> (int, bool)

fn (x, wid : (([A] (A) -> A) -> int)) { wid(fn(a){{x:x(a),y:a}.y}) }
> fn (x, wid: (([A] (A) -> A) -> int)) { wid(fn (a) { {x: x(a), y: a}.y }) }
> * ⊢ (⊤, (∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0) → int) → int
> (any, ([A] (A) -> A) -> int) -> int

fn (x, wid : (([A <: {foo:int}, A :> {foo:int,bar:string}] (A) -> A) -> int)) { wid(fn(a){x(a)}) }
> fn (x, wid: (([A <: {foo: int}, A :> {foo: int, bar: string}] (A) -> A) -> int)) { wid(fn (a) { x(a) }) }
> *
> ⊢
> (
>   ((foo: int)) → (foo: int, bar: string),
>   (∀⁺ 0:[(foo: int, bar: string),(foo: int)]. (.0.0) → .0.0) → int) → int
> (({foo: int}) -> {foo: int, bar: string}, ([A <: {foo: int}, A :> {foo: int, bar: string}] (A) -> A) -> int) -> int

fn(f) { (fn(x) { 5 })(f(10)) }
> fn (f) { (fn (x) { 5 })(f(10)) }
> * ⊢ ((int) → ⊤) → int
> ((int) -> any) -> int


# needs approx
(fn (x) { x })(fn (x) { x })
> (fn (x) { x })(fn (x) { x })
> *, 0: [(#1.2) → #1.1, ⊤], 1: [#1.2, ⊤], 2: [⊥, #1.1],  ⊢ #1.0
> [A] (A) -> A

# generalised version
fn() { (fn (x) { x })(fn (x) { x }) }
> fn () { (fn (x) { x })(fn (x) { x }) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → (.0.0) → .0.0
> [A] () -> (A) -> A

# self-app
(fn (x) { x(x) }) (fn (x) { x(x) })
> (fn (x) { x(x) })(fn (x) { x(x) })
> typechecking error: Stack overflow
