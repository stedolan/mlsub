# FIXME: currently using internal syntax (Typedefs.pr_*)

#
# Literals
#

0
> 0
> * ⊢ int
>   0
> int

5
> 5
> * ⊢ int
>   5
> int

true
> true
> * ⊢ bool
>   true
> bool

false
> false
> * ⊢ bool
>   false
> bool

# FIXME: string syntax
# FIXME: interesting numeric literals (negative, hex, float, etc.)

# checking forms

(42 : int)
> (42 : int)
> * ⊢ int
>   (42 : int)
> int

(true : bool)
> (true : bool)
> * ⊢ bool
>   (true : bool)
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
>   if (true){1} else {2}
> int

if (false) { 1 } else { false }
> if (false){1} else {false}
> * ⊢ ⊤
>   if (false){1} else {false}
> any

#
# Tuples
#

(1, 2)
> (1, 2)
> * ⊢ (int, int)
>   (1, 2)
> (int, int)

(true, 3, 4)
> (true, 3, 4)
> * ⊢ (bool, int, int)
>   (true, 3, 4)
> (bool, int, int)

# python-style singleton tuples
(4,)
> (4,)
> * ⊢ (int)
>   (4,)
> (int,)

{foo:1}
> {foo: 1}
> * ⊢ (foo: int)
>   {foo: 1}
> {foo: int}

# not a singleton tuple
(1)
> (1)
> * ⊢ int
>   (1)
> int

# arity
((1,),(2,3),(4,5,6),(7,8,9,10))
> ((1,), (2, 3), (4, 5, 6), (7, 8, 9, 10))
> * ⊢ ((int), (int, int), (int, int, int), (int, int, int, int))
>   ((1,), (2, 3), (4, 5, 6), (7, 8, 9, 10))
> ((int,), (int, int), (int, int, int), (int, int, int, int))

# empty tuple (unit type)
()
> ()
> * ⊢ ()
>   ()
> ()

# trailing comma in types, too
((1,) : (int,))
> ((1,) : (int,))
> * ⊢ (int)
>   ((1,) : (int,))
> (int,)

((1,) : (int))
> ((1,) : (int))
> typechecking error: Failure("incompat")

# and patterns
let (x,) = (1,); {x}
> let (x,) = (1,); {x}
> * ⊢ (x: int)
>   let (x,) : (int,) = (1,); {x}
> {x: int}

let (x) = (1,); {x}
> let (x) = (1,); {x}
> * ⊢ (x: (int))
>   let (x) : (int,) = (1,); {x}
> {x: (int,)}

# named fields
({foo:20, bar:17}, {baz:1})
> ({foo: 20, bar: 17}, {baz: 1})
> * ⊢ ((foo: int, bar: int), (baz: int))
>   ({foo: 20, bar: 17}, {baz: 1})
> ({foo: int, bar: int}, {baz: int})

# FIXME mixture of named and unnamed
# (1, 2, .bar=3, .baz=true)
# > * ⊢ (int, int, bar: int, baz: bool)

# joins
if (true) { (1, 2) } else { (1, true, 3) }
> if (true){(1, 2)} else {(1, true, 3)}
> * ⊢ (int, ⊤, ...)
>   if (true){(1, 2)} else {(1, true, 3)}
> (int, any, ...)

if (false) { {foo:1,bar:2} } else { {foo:1,baz:()} }
> if (false){{foo: 1, bar: 2}} else {{foo: 1, baz: ()}}
> * ⊢ (foo: int, ...)
>   if (false){{foo: 1, bar: 2}} else {{foo: 1, baz: ()}}
> {foo: int, ...}

((1,2,3) : (int,int))
> ((1, 2, 3) : (int, int))
> typechecking error: Failure("extra")

((1,2,asdf) : (int, int, ...))
> ((1, 2, asdf) : (int, int, ...))
> typechecking error: Failure("asdf not in scope")

((1,2,3) : (int, int, ...))
> ((1, 2, 3) : (int, int, ...))
> * ⊢ (int, int, ...)
>   ((1, 2) : (int, int, ...))
> (int, int, ...)


true.foo
> true.foo
> typechecking error: Failure("incompat")

@bot
> @bot
> * ⊢ ⊥
>   @bot
> nothing

# checking join of functions and meet of records
if true { (@bot : (~foo:(int,int), ~bar:any) -> string) } else { (@bot : (~foo:(int,int), ~bar:any) -> string) }
> if true{(@bot : (~foo: (int, int), ~bar: any) -> string)} else {(@bot : (~foo: (int, int), ~bar: any) -> string)}
> * ⊢ (foo: (int, int), bar: ⊤) → string
>   if true{(@bot : (~foo: (int, int), ~bar: any) -> string)} else
>   {(@bot : (~foo: (int, int), ~bar: any) -> string)}
> (~foo: (int, int), ~bar: any) -> string

if true { (@bot : ((int,any), ~foo:(int,int), ~bar:any) -> string) } else {(@bot : ((any,string), ~bar:string, ~foo:(string,any)) -> nothing)}
> if true{(@bot : ((int, any), ~foo: (int, int), ~bar: any) -> string)} else
> {(@bot : ((any, string), ~bar: string, ~foo: (string, any)) -> nothing)}
> * ⊢ ((int, string), foo: (⊥, int), bar: string) → string
>   if true{(@bot : ((int, any), ~foo: (int, int), ~bar: any) -> string)} else
>   {(@bot : ((any, string), ~bar: string, ~foo: (string, any)) -> nothing)}
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
>   (@true : bool)
> bool

((@true, @false) : (bool, bool))
> ((@true, @false) : (bool, bool))
> * ⊢ (bool, bool)
>   ((@true, @false) : (bool, bool))
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
>   ((1, 2) : (int, int, ...))
> (int, int, ...)

((1, 2, 3) : (int, int, ...))
> ((1, 2, 3) : (int, int, ...))
> * ⊢ (int, int, ...)
>   ((1, 2) : (int, int, ...))
> (int, int, ...)


# A checking form for projections! Isn't subtyping great?
({foo: @true}.foo : bool)
> ({foo: @true}.foo : bool)
> * ⊢ bool
>   ({foo: @true}.foo : bool)
> bool

# Generalisation of functions allows checking against inferred argument types
(fn(x) { if x.cond { 1 } else { 2 }})({cond: @true})
> (fn (x) { if x.cond{1} else {2} })({cond: @true})
> typechecking error: Failure("pragma: true")

#
# Let-bindings and patterns
#

let x = 1; x
> let x = 1; x
> * ⊢ int
>   let x : int = 1; x
> int

(let x = @true; x : bool)
> (let x = @true; x : bool)
> typechecking error: Failure("pragma: true")

(let x : bool = @true; (x, @false) : (bool,bool))
> (let x : bool = @true; (x, @false) : (bool, bool))
> * ⊢ (bool, bool)
>   (let x : bool = @true; (x, @false) : (bool, bool))
> (bool, bool)

let x = (1, 2); x
> let x = (1, 2); x
> * ⊢ (int, int)
>   let x : (int, int) = (1, 2); x
> (int, int)

let x : int = (1, 2); x
> let x : int = (1, 2); x
> typechecking error: Failure("incompat")

let x : bool = true; x
> let x : bool = true; x
> * ⊢ bool
>   let x : bool = true; x
> bool

let x : bool = 5; x
> let x : bool = 5; x
> typechecking error: Failure("incompat")

let {x: foo, y: bar} = {x: 10, y: true}; (foo, bar)
> let {x: foo, y: bar} = {x: 10, y: true}; (foo, bar)
> * ⊢ (int, bool)
>   let {x: foo, y: bar} : {x: int, y: bool} = {x: 10, y: true}; (foo, bar)
> (int, bool)

let {x: foo, y: bar} = {x: 10, y: true, z: 42}; (foo, bar)
> let {x: foo, y: bar} = {x: 10, y: true, z: 42}; (foo, bar)
> typechecking error: Failure("extra")

let {x: foo, y: bar, ...} = {x: 10, y: true, z: 42}; (foo, bar)
> let {x: foo, y: bar, ...} = {x: 10, y: true, z: 42}; (foo, bar)
> * ⊢ (int, bool)
>   let {x: foo, y: bar, ...} : {x: int, y: bool, z: int} =
>   {x: 10, y: true, z: 42};
>   (foo, bar)
> (int, bool)


# Tuple bindings

let (x, y) = (1, true); (y, x)
> let (x, y) = (1, true); (y, x)
> * ⊢ (bool, int)
>   let (x, y) : (int, bool) = (1, true); (y, x)
> (bool, int)

let (x, y, ...) = (false, (), 3); {x,y}
> let (x, y, ...) = (false, (), 3); {x, y}
> * ⊢ (x: bool, y: ())
>   let (x, y, ...) : (bool, (), int) = (false, (), 3); {x, y}
> {x: bool, y: ()}


let {x: foo, y: bar} : {x:int, y:bool} = {x:1, y:true}; foo
> let {x: foo, y: bar} : {x: int, y: bool} = {x: 1, y: true}; foo
> * ⊢ int
>   let {x: foo, y: bar} : {x: int, y: bool} = {x: 1, y: true}; foo
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
>   let {x, y} : {x: int, y: bool} = {x: 1, y: true}; (y, x)
> (bool, int)

let {x, y} = {x:1, y:true}; (y,x)
> let {x, y} = {x: 1, y: true}; (y, x)
> * ⊢ (bool, int)
>   let {x, y} : {x: int, y: bool} = {x: 1, y: true}; (y, x)
> (bool, int)

let {x, y} = {x:1, y:true}; {y,x,z:3}
> let {x, y} = {x: 1, y: true}; {y, x, z: 3}
> * ⊢ (y: bool, x: int, z: int)
>   let {x, y} : {x: int, y: bool} = {x: 1, y: true}; {y, x, z: 3}
> {y: bool, x: int, z: int}

let {x, y} = {x:1, y:true}; ({y,x,z:3} : {y: bool, x: int, z: int})
> let {x, y} = {x: 1, y: true}; ({y, x, z: 3} : {y: bool, x: int, z: int})
> * ⊢ (y: bool, x: int, z: int)
>   let {x, y} : {x: int, y: bool} = {x: 1, y: true};
>   ({y, x, z: 3} : {y: bool, x: int, z: int})
> {y: bool, x: int, z: int}


# subtyping checks. FIXME: these probably only hit matching :(
let a = {foo: 1, bar: 2}; let b : {foo: int, bar: int} = a; b
> let a = {foo: 1, bar: 2}; let b : {foo: int, bar: int} = a; b
> * ⊢ (foo: int, bar: int)
>   let a : {foo: int, bar: int} = {foo: 1, bar: 2};
>   let b : {foo: int, bar: int} = a;
>   b
> {foo: int, bar: int}

let a = {foo: 1, bar: 2}; let b : {bar: int} = a; b
> let a = {foo: 1, bar: 2}; let b : {bar: int} = a; b
> typechecking error: Failure("extra")

let a = {foo: 1, bar: 2}; let b : {bar: any, ...} = a; b
> let a = {foo: 1, bar: 2}; let b : {bar: any, ...} = a; b
> * ⊢ (bar: ⊤, ...)
>   let a : {foo: int, bar: int} = {foo: 1, bar: 2};
>   let b : {bar: any, ...} = a;
>   b
> {bar: any, ...}

let a = {foo: 1, bar: 2}; let b : {bar: nothing, ...} = a; b
> let a = {foo: 1, bar: 2}; let b : {bar: nothing, ...} = a; b
> typechecking error: Failure("incompat")

# function types
fn (f: (int,int) -> int) { f(1,2) }
> fn (f: (int, int) -> int) { f(1, 2) }
> * ⊢ ((int, int) → int) → int
>   fn (f: (int, int) -> int) : int { f(1, 2) }
> ((int, int) -> int) -> int

fn (f: (~x:int,~y:int) -> int) { f(~x:1, ~y:2) }
> fn (f: (~x: int, ~y: int) -> int) { f(~x: 1, ~y: 2) }
> * ⊢ ((x: int, y: int) → int) → int
>   fn (f: (~x: int, ~y: int) -> int) : int { f(~x: 1, ~y: 2) }
> ((~x: int, ~y: int) -> int) -> int

fn (f: (~x:int,~y:int) -> int) { let x = 1; f(~x, ~y:2) }
> fn (f: (~x: int, ~y: int) -> int) { let x = 1; f(~x, ~y: 2) }
> * ⊢ ((x: int, y: int) → int) → int
>   fn (f: (~x: int, ~y: int) -> int) : int { let x : int = 1; f(~x, ~y: 2) }
> ((~x: int, ~y: int) -> int) -> int

fn () { (fn (~x, ~y) { {x,y} }) (~y:1, ~x:()) }
> fn () { (fn (~x, ~y) { {x, y} })(~y: 1, ~x: ()) }
> * ⊢ () → (x: (), y: int)
>   fn () : {x: (), y: int} {
>   (fn [A, B](~x : A, ~y : B) : {x: A, y: B} { {x, y} })(~y: 1, ~x: ())
>   }
> () -> {x: (), y: int}

(fn (x) { x } : (int,int) -> int)
> (fn (x) { x } : (int, int) -> int)
> typechecking error: Failure("extra")

(fn (x,y) { x } : (int) -> int)
> (fn (x, y) { x } : (int) -> int)
> typechecking error: Failure("missing .1")

#
# Lambda
#

fn (a, b) { (b, a.foo) }
> fn (a, b) { (b, a.foo) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((foo: .0.1, ...), .0.0) → (.0.0, .0.1)
>   fn [A, B](a: {foo: B, ...}, b: A) : (A, B) { (b, a.foo) }
> [A, B] ({foo: B, ...}, A) -> (A, B)

fn (a, b) : int { b }
> fn (a, b) : int { b }
> * ⊢ (⊤, int) → int
>   fn (a: any, b: int) : int { b }
> (any, int) -> int

fn (a : int, b) : (int, int) { (a, b) }
> fn (a: int, b) : (int, int) { (a, b) }
> * ⊢ (int, int) → (int, int)
>   fn (a: int, b: int) : (int, int) { (a, b) }
> (int, int) -> (int, int)

(fn (a) { (a, @true) } : (int) -> (int, bool))
> (fn (a) { (a, @true) } : (int) -> (int, bool))
> typechecking error: Failure("pragma: true")

fn (a) { if (a.foo) { {bar: a.bar} } else { a } }
> fn (a) { if (a.foo){{bar: a.bar}} else {a} }
> *
> ⊢
> ∀⁺ 0:[⊥,(foo: bool, bar: .0.1, ...)], 1:[⊥,⊤], 2:[(bar: .0.1),⊤],
> 0 ≤ 2. (.0.0) → .0.2
>   fn [A <: {foo: bool, bar: B, ...}, B, C :> {bar: B}, A <: C](a: A) : C {
>   if (a.foo){{bar: a.bar}} else
>   {a}
>   }
> [A <: {foo: bool, bar: B, ...}, B, C :> {bar: B}, A <: C] (A) -> C

(fn (a) { a })(5)
> (fn (a) { a })(5)
> * ⊢ int
>   (fn [A](a: A) : A { a })(5)
> int

# tricky: the second 5 should be checked against Top (i.e. inferred)
(fn (a,b) { a })(5,5)
> (fn (a, b) { a })(5, 5)
> * ⊢ int
>   (fn [A](a: A, b: any) : A { a })(5, 5)
> int
(fn (a,b) { a })(5,if 5 { 5 } else { 5 })
> (fn (a, b) { a })(5, if 5{5} else {5})
> typechecking error: Failure("incompat")

# more tuple cases
fn (f) { (f({x:1,y:2}), f({x:1,z:2})) }
> fn (f) { (f({x: 1, y: 2}), f({x: 1, z: 2})) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (((x: int, ...)) → .0.0) → (.0.0, .0.0)
>   fn [A](f: ({x: int, ...}) -> A) : (A, A) { (f({x: 1, y: 2}), f({x: 1, z: 2})) }
> [A] (({x: int, ...}) -> A) -> (A, A)

fn (x) { if x.cond { {p:1} } else { {p:2,q:1} } }
> fn (x) { if x.cond{{p: 1}} else {{p: 2, q: 1}} }
> * ⊢ ((cond: bool, ...)) → (p: int, ...)
>   fn (x: {cond: bool, ...}) : {p: int, ...} {
>   if x.cond{{p: 1}} else
>   {{p: 2, q: 1}}
>   }
> ({cond: bool, ...}) -> {p: int, ...}

fn (x) { if x.cond { {q:2,p:1} } else { {p:2,q:1} } }
> fn (x) { if x.cond{{q: 2, p: 1}} else {{p: 2, q: 1}} }
> * ⊢ ((cond: bool, ...)) → (q: int, p: int)
>   fn (x: {cond: bool, ...}) : {q: int, p: int} {
>   if x.cond{{q: 2, p: 1}} else
>   {{p: 2, q: 1}}
>   }
> ({cond: bool, ...}) -> {q: int, p: int}

fn (x) { let {p,q,...}=x; x }
> fn (x) { let {p, q, ...} = x; x }
> * ⊢ ∀⁺ 0:[⊥,(p: ⊤, q: ⊤, ...)]. (.0.0) → .0.0
>   fn [A <: {p: any, q: any, ...}](x: A) : A { let {p, q, ...} : A = x; x }
> [A <: {p: any, q: any, ...}] (A) -> A

fn (x) { let {p,q} = x; let {p,q,r} = x; {p,q} }
> fn (x) { let {p, q} = x; let {p, q, r} = x; {p, q} }
> * ⊢ ∀⁺ 0:[⊥,⊥]. (.0.0) → (p: ⊥, q: ⊥)
>   fn [A <: nothing](x: A) : {p: nothing, q: nothing} {
>   let {p, q} : A = x;
>   let {p, q, r} : A = x;
>   {p, q}
>   }
> [A <: nothing] (A) -> {p: nothing, q: nothing}

fn (x) { let {p,q,...} = x; let {p,q,r} = x; {p,q} }
> fn (x) { let {p, q, ...} = x; let {p, q, r} = x; {p, q} }
> *
> ⊢
> ∀⁺ 0:[⊥,(p: .0.1, q: .0.2, r: ⊤)], 1:[⊥,⊤], 2:[⊥,⊤]. (.0.0) → (p: .0.1, q: .0.2)
>   fn [A <: {p: B, q: C, r: any}, B, C](x: A) : {p: B, q: C} {
>   let {p, q, ...} : A = x;
>   let {p, q, r} : A = x;
>   {p, q}
>   }
> [A <: {p: B, q: C, r: any}, B, C] (A) -> {p: B, q: C}

fn (x) { let {p,q} = x; let {p,q,r,...} = x; {p,q} }
> fn (x) { let {p, q} = x; let {p, q, r, ...} = x; {p, q} }
> * ⊢ ∀⁺ 0:[⊥,⊥]. (.0.0) → (p: ⊥, q: ⊥)
>   fn [A <: nothing](x: A) : {p: nothing, q: nothing} {
>   let {p, q} : A = x;
>   let {p, q, r, ...} : A = x;
>   {p, q}
>   }
> [A <: nothing] (A) -> {p: nothing, q: nothing}

fn (x) { let {p,q,...} = x; let {p,q,r,...} = x; {p,q} }
> fn (x) { let {p, q, ...} = x; let {p, q, r, ...} = x; {p, q} }
> *
> ⊢
> ∀⁺ 0:[⊥,(p: .0.1, q: .0.2, r: ⊤, ...)], 1:[⊥,⊤], 2:[⊥,⊤]. (.0.0) → (
>   p: .0.1,
>   q: .0.2)
>   fn [A <: {p: B, q: C, r: any, ...}, B, C](x: A) : {p: B, q: C} {
>   let {p, q, ...} : A = x;
>   let {p, q, r, ...} : A = x;
>   {p, q}
>   }
> [A <: {p: B, q: C, r: any, ...}, B, C] (A) -> {p: B, q: C}


fn(b) { (fn (a) { if (a.cond) { a } else { a } })(if true { b } else { {foo: 1, cond: false} }) }
> fn (b) { (fn (a) { if (a.cond){a} else {a} })(if true{b} else {{foo: 1, cond: false}}) }
> * ⊢ ∀⁺ 0:[(foo: int, cond: bool),(cond: bool, ...)]. (.0.0) → .0.0
>   fn [A <: {cond: bool, ...}, A :> {foo: int, cond: bool}](b: A) : A {
>   (fn [B <: {cond: bool, ...}](a: B) : B { if (a.cond){a} else {a} })(if true{b} else
>   {{foo: 1, cond: false}})
>   }
> [A <: {cond: bool, ...}, A :> {foo: int, cond: bool}] (A) -> A

fn(b) { if (b.cond) { b } else { {foo: 1, cond: false} } }
> fn (b) { if (b.cond){b} else {{foo: 1, cond: false}} }
> *
> ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[(foo: int, cond: bool),⊤], 0 ≤ 1. (.0.0) → .0.1
>   fn [A <: {cond: bool, ...}, B :> {foo: int, cond: bool}, A <: B](b: A) : B {
>   if (b.cond){b} else
>   {{foo: 1, cond: false}}
>   }
> [A <: {cond: bool, ...}, B :> {foo: int, cond: bool}, A <: B] (A) -> B

fn(b) { if (b.cond) { b } else { {foo: 1, cond: 4} } }
> fn (b) { if (b.cond){b} else {{foo: 1, cond: 4}} }
> *
> ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[(foo: int, cond: int),⊤], 0 ≤ 1. (.0.0) → .0.1
>   fn [A <: {cond: bool, ...}, B :> {foo: int, cond: int}, A <: B](b: A) : B {
>   if (b.cond){b} else
>   {{foo: 1, cond: 4}}
>   }
> [A <: {cond: bool, ...}, B :> {foo: int, cond: int}, A <: B] (A) -> B

fn (x) { (x.foo, x.bar, x.foo) }
> fn (x) { (x.foo, x.bar, x.foo) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((foo: .0.0, bar: .0.1, ...)) → (.0.0, .0.1, .0.0)
>   fn [A, B](x: {foo: A, bar: B, ...}) : (A, B, A) { (x.foo, x.bar, x.foo) }
> [A, B] ({foo: A, bar: B, ...}) -> (A, B, A)

fn (x) { if (x.cond) { (x.foo, x.bar) } else { (x.foo, x.foo) } }
> fn (x) { if (x.cond){(x.foo, x.bar)} else {(x.foo, x.foo)} }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤],
> 0 ≤ 1. ((cond: bool, foo: .0.0, bar: .0.1, ...)) → (.0.0, .0.1)
>   fn [A, B, A <: B](x: {cond: bool, foo: A, bar: B, ...}) : (A, B) {
>   if (x.cond){(x.foo, x.bar)} else
>   {(x.foo, x.foo)}
>   }
> [A, B, A <: B] ({cond: bool, foo: A, bar: B, ...}) -> (A, B)

fn (x) { ((fn(x){x.foo})(x), (fn(x){x.foo})(x))  }
> fn (x) { ((fn (x) { x.foo })(x), (fn (x) { x.foo })(x)) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((foo: .0.0, ...)) → (.0.0, .0.0)
>   fn [A](x: {foo: A, ...}) : (A, A) {
>   ((fn [B](x: {foo: B, ...}) : B { x.foo })(x),
>   (fn [B](x: {foo: B, ...}) : B { x.foo })(x))
>   }
> [A] ({foo: A, ...}) -> (A, A)

# nested constraints, garbage variables
fn (x) { (fn(y) { y.foo.bar })({foo:{bar:x}}) }
> fn (x) { (fn (y) { y.foo.bar })({foo: {bar: x}}) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0
>   fn [A](x: A) : A {
>   (fn [B](y: {foo: {bar: B, ...}, ...}) : B { y.foo.bar })({foo: {bar: x}})
>   }
> [A] (A) -> A

# Trying to make an example with meets/joins under ctors in bounds
fn (x, f, g) { ( f(x.foo), g(x.foo) ) }
> fn (x, f, g) { (f(x.foo), g(x.foo)) }
> *
> ⊢
> ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 2:[⊥,⊤]. ((foo: .0.2, ...), (.0.2) → .0.0, (.0.2) → .0.1) → (
>   .0.0,
>   .0.1)
>   fn [A, B, C](x: {foo: C, ...}, f: (C) -> A, g: (C) -> B) : (A, B) {
>   (f(x.foo), g(x.foo))
>   }
> [A, B, C] ({foo: C, ...}, (C) -> A, (C) -> B) -> (A, B)

# same example in garbage position
(fn(x) { 5 }) (fn (x, f, g) { ( f(x.foo), g(x.foo) ) })
> (fn (x) { 5 })(fn (x, f, g) { (f(x.foo), g(x.foo)) })
> * ⊢ int
>   (fn (x: any) : int { 5 })(fn [A, B, C](x: {foo: C, ...},
>   f: (C) ->
>   A,
>   g: (C) ->
>   B) : (A, B) { (f(x.foo), g(x.foo)) })
> int

# garbage
fn (x) { (fn (y) { 5 })(if (x.cond) { (x.a, x.b) } else { (x.b, x.a) }) }
> fn (x) { (fn (y) { 5 })(if (x.cond){(x.a, x.b)} else {(x.b, x.a)}) }
> * ⊢ ((cond: bool, a: ⊤, b: ⊤, ...)) → int
>   fn (x: {cond: bool, a: any, b: any, ...}) : int {
>   (fn (y: any) : int { 5 })(if (x.cond){(x.a, x.b)} else {(x.b, x.a)})
>   }
> ({cond: bool, a: any, b: any, ...}) -> int


fn (x) { if (x.cond) { (x.a, x.b) } else { (x.b, x.a) } }
> fn (x) { if (x.cond){(x.a, x.b)} else {(x.b, x.a)} }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((cond: bool, a: .0.0, b: .0.0, ...)) → (.0.0, .0.0)
>   fn [A](x: {cond: bool, a: A, b: A, ...}) : (A, A) {
>   if (x.cond){(x.a, x.b)} else
>   {(x.b, x.a)}
>   }
> [A] ({cond: bool, a: A, b: A, ...}) -> (A, A)

fn (x) { if (x.cond) { (x, 5) } else { (x, x) } }
> fn (x) { if (x.cond){(x, 5)} else {(x, x)} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool, ...)], 1:[int,⊤], 0 ≤ 1. (.0.0) → (.0.0, .0.1)
>   fn [A <: {cond: bool, ...}, B :> int, A <: B](x: A) : (A, B) {
>   if (x.cond){(x, 5)} else
>   {(x, x)}
>   }
> [A <: {cond: bool, ...}, B :> int, A <: B] (A) -> (A, B)

fn (x) { if (x.cond) { (x, 5) } else { (x, x.n) } }
> fn (x) { if (x.cond){(x, 5)} else {(x, x.n)} }
> * ⊢ ∀⁺ 0:[⊥,(cond: bool, n: .0.1, ...)], 1:[int,⊤]. (.0.0) → (.0.0, .0.1)
>   fn [A <: {cond: bool, n: B, ...}, B :> int](x: A) : (A, B) {
>   if (x.cond){(x, 5)} else
>   {(x, x.n)}
>   }
> [A <: {cond: bool, n: B, ...}, B :> int] (A) -> (A, B)

# once
# this is a very disappointing type. The α/γ pair needs to go!
fn (f, x) { f(x) }
> fn (f, x) { f(x) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((.0.1) → .0.0, .0.1) → .0.0
>   fn [A, B](f: (B) -> A, x: B) : A { f(x) }
> [A, B] ((B) -> A, B) -> A

# twice!
fn (f, x) { f(f(x)) }
> fn (f, x) { f(f(x)) }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤], 0 ≤ 1. ((.0.1) → .0.0, .0.1) → .0.0
>   fn [A, B, A <: B](f: (B) -> A, x: B) : A { f(f(x)) }
> [A, B, A <: B] ((B) -> A, B) -> A

# can I hit approx with nested lambda-generalisations? trickier than I thought.
fn (f) { fn(x) { (f(x), x) } }
> fn (f) { fn (x) { (f(x), x) } }
> * ⊢ ∀⁺ 0:[⊥,⊤], 1:[⊥,⊤]. ((.0.1) → .0.0) → ∀⁺ 0:[⊥,.1.1]. (.0.0) → (.1.0, .0.0)
>   fn [A, B](f: (B) -> A) : [C <: B] (C) ->
>   (A, C) { fn [C <: B](x: C) : (A, C) { (f(x), x) } }
> [A, B] ((B) -> A) -> [C <: B] (C) -> (A, C)


# poly id as an argument!
fn (f) { (f(1), f(true)) }
> fn (f) { (f(1), f(true)) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. ((⊤) → .0.0) → (.0.0, .0.0)
>   fn [A](f: (any) -> A) : (A, A) { (f(1), f(true)) }
> [A] ((any) -> A) -> (A, A)

fn (f : [A] (A) -> A) { (f(1), f(true)) }
> fn (f: [A] (A) -> A) { (f(1), f(true)) }
> * ⊢ (∀⁻ 0:[⊥,⊤]. (.0.0) → .0.0) → (int, bool)
>   fn (f: [A] (A) -> A) : (int, bool) { (f(1), f(true)) }
> ([A] (A) -> A) -> (int, bool)

fn (x, wid : (([A] (A) -> A) -> int)) { wid(fn(a){{x:x(a),y:a}.y}) }
> fn (x, wid: (([A] (A) -> A) -> int)) { wid(fn (a) { {x: x(a), y: a}.y }) }
> * ⊢ ∀⁺ 0:[⊤,⊤]. ((.0.0) → ⊤, (∀⁺ 0:[⊥,⊤]. (.0.0) → .0.0) → int) → int
>   fn [A :> any](x: (A) -> any, wid: ([A_2] (A_2) -> A_2) -> int) : int {
>   wid(fn [B <: A](a: B) : B { {x: x(a), y: a}.y })
>   }
> [A :> any] ((A) -> any, ([A_2] (A_2) -> A_2) -> int) -> int

fn (x, wid : (([A <: {foo:int}, A :> {foo:int,bar:string}] (A) -> A) -> int)) { wid(fn(a){x(a)}) }
> fn (x, wid: (([A <: {foo: int}, A :> {foo: int, bar: string}] (A) -> A) -> int)) { wid(fn (a) { x(a) }) }
> *
> ⊢
> ∀⁺ 0:[⊥,(foo: int, bar: string)], 1:[(foo: int),⊤]. (
>   (.0.1) → .0.0,
>   (∀⁺ 0:[(foo: int, bar: string),(foo: int)]. (.0.0) → .0.0) → int) → int
>   fn [A <: {foo: int, bar: string}, B :> {foo: int}](x: (B) ->
>   A,
>   wid: ([A_2 <: {foo: int}, A_2 :> {foo: int, bar: string}] (A_2) -> A_2) ->
>   int) : int { wid(fn (a: B) : A { x(a) }) }
> [A <: {foo: int, bar: string}, B :> {foo: int}] ((B) ->
> A,
> ([A_2 <: {foo: int}, A_2 :> {foo: int, bar: string}] (A_2) -> A_2) ->
> int) ->
> int

fn(f) { (fn(x) { 5 })(f(10)) }
> fn (f) { (fn (x) { 5 })(f(10)) }
> * ⊢ ((int) → ⊤) → int
>   fn (f: (int) -> any) : int { (fn (x: any) : int { 5 })(f(10)) }
> ((int) -> any) -> int


# FIXME: fails recheck. Is this a correct value restriction?
# # needs approx
# (fn (x) { x })(fn (x) { x })
# > (fn (x) { x })(fn (x) { x })
# > *, 0: [(#1.2) → #1.1, ⊤], 1: [#1.2, ⊤], 2: [⊥, #1.1],  ⊢ #1.0
# > [A] (A) -> A

# generalised version
fn() { (fn (x) { x })(fn (x) { x }) }
> fn () { (fn (x) { x })(fn (x) { x }) }
> * ⊢ ∀⁺ 0:[⊥,⊤]. () → (.0.0) → .0.0
>   fn [A]() : (A) -> A { (fn [B](x: B) : B { x })(fn [B](x: B) : B { x }) }
> [A] () -> (A) -> A

# self-app
(fn (x) { x(x) }) (fn (x) { x(x) })
> (fn (x) { x(x) })(fn (x) { x(x) })
> typechecking error: Stack overflow
