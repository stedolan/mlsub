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

(.foo=1)
> * ⊢ (foo: int)

(.foo=1,)
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
((.foo=20, .bar=17), (.baz=1))
> * ⊢ ((foo: int, bar: int), (baz: int))

# mixture of named and unnamed
(1, 2, .bar=3, .baz=true)
> * ⊢ (int, int, bar: int, baz: bool)

# joins
if (true) { (1, 2) } else { (1, true, 3) }
> * ⊢ (int, ⊤, ...)

if (false) { (.foo=1,.bar=2) } else { (.foo=1,.baz=()) }
> * ⊢ (foo: int, ...)

true.foo
> typechecking error: Failure("incompat")

@bot
> * ⊢ ⊥

# checking join of functions and meet of records
if true { (@bot : (.foo:(int,int), .bar:any) -> string) } else { (@bot : (.foo:(int,int), .bar:any) -> string) }
> * ⊢ (foo: (int, int), bar: ⊤) → string

if true { (@bot : ((int,any), .foo:(int,int), .bar:any) -> string) } else {(@bot : ((any,string), .bar:string, .foo:(string,any)) -> nothing)}
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
(1, 2, ...)
> * ⊢ (int, int, ...)

((1, 2) : (int, int, ...))
> * ⊢ (int, int, ...)

# FIXME: should this be allowed?
# ((1, 2, 3) : (int, int, ...))


# A checking form for projections! Isn't subtyping great?
((.foo = @true).foo : bool)
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

let (.x as foo, .y as bar) = (.x = 10, .y = true); (foo, bar)
> * ⊢ (int, bool)

let (.x as foo, .y as bar) = (.x = 10, .y = true, .z = 42); (foo, bar)
> typechecking error: Failure("extra")

let (.x as foo, .y as bar, ...) = (.x = 10, .y = true, .z = 42); (foo, bar)
> * ⊢ (int, bool)


# Multiple bindings vs. tuple bindings

let (x, y) = (1, true); (y, x)
> * ⊢ (bool, int)

let x, y = 1, true; (y, x)
> * ⊢ (bool, int)

let (x, y) = 1, true; (y, x)
> typechecking error: Failure("incompat")

let x, y = (1, true); (y, x)
> typechecking error: Failure("extra patterns")


let (.x as foo, .y as bar) : (.x:int, .y:bool) = (.x=1, .y=true); foo
> * ⊢ int
let (.x as foo, .y as bar) : (.x:int) = (.x=1, .y=true); foo
> typechecking error: Failure("extra")
let (.x as foo, .y as bar) : (.x:int,.y:int) = (.x=1, .y=true); foo
> typechecking error: Failure("incompat")
let (.x as foo, .y as bar) : (.x:int,.y:bool,.z:bool) = (.x=1, .y=true); foo
> typechecking error: Failure("missing z")

let x, y = 1, true; (y, x)
> * ⊢ (bool, int)

# punning

let (.x, .y) : (.x:int, .y:bool) = (.x=1, .y=true); (y,x)
> * ⊢ (bool, int)

let (.x, .y) = (.x=1, .y=true); (y,x)
> * ⊢ (bool, int)

let (.x, .y) = (.x=1, .y=true); (.y,.x,.z=3)
> * ⊢ (y: bool, x: int, z: int)

let (.x, .y) = (.x=1, .y=true); ((.y,.x,.z=3) : (.y: bool, .x: int, .z: int))
> typechecking error: Failure("punning unimplemented")


# subtyping checks. FIXME: these probably only hit matching :(
let a = (.foo = 1, .bar = 2); let b : (.foo: int, .bar: int) = a; b
> * ⊢ (foo: int, bar: int)

let a = (.foo = 1, .bar = 2); let b : (.bar: int) = a; b
> typechecking error: Failure("extra")

let a = (.foo = 1, .bar = 2); let b : (.bar: any, ...) = a; b
> * ⊢ (bar: ⊤, ...)

let a = (.foo = 1, .bar = 2); let b : (.bar: nothing, ...) = a; b
> typechecking error: Failure("incompat")


#
# Lambda
#

fn (a, b) { (b, a.foo) }
> 'α: [⊥, ⊤], 'β: [⊥, ⊤], * ⊢ ((foo: 'β, ...), 'α) → ('α, 'β)

fn (a, b) : int { b }
> * ⊢ (⊤, int) → int

fn (a : int, b) : (int, int) { (a, b) }
> * ⊢ (int, int) → (int, int)

(fn (a) { (a, @true) } : (int) -> (int, bool))
> * ⊢ (int) → (int, bool)

fn (a) { if (a.foo) { (.bar=a.bar) } else { a } }
> 'α: [⊥, (foo: bool, bar: 'β, ...)], 'β: [⊥, ⊤], * ⊢ ('α) → ((bar: 'β)) ⊔ 'α

(fn (a) { a })(5)
> * ⊢ int

# tricky: the second 5 should be checked against Top (i.e. inferred)
(fn (a,...) { a })(5,5)
> * ⊢ int
(fn (a,...) { a })(5,if 5 { 5 } else { 5 })
> typechecking error: Failure("incompat")


fn(b) { (fn (a) { if (a.cond) { a } else { a } })(if true { b } else { (.foo = 1, .cond = false) }) }
> 'α: [⊥, ((cond: bool, ...)) ⊓ 'β],
> 'β: [((foo: int, cond: bool)) ⊔ 'α, (cond: bool, ...)],
> *
> ⊢ ('α) → 'β

# once
# this is a very disappointing type. The α/γ pair needs to go!
fn (f, x) { f(x) }
> 'α: [⊥, 'γ], 'β: [⊥, ⊤], 'γ: ['α, ⊤], * ⊢ (('γ) → 'β, 'α) → 'β

# twice!
fn (f, x) { f(f(x)) }
> 'α: [⊥, 'ε], 'β: [⊥, ⊤], 'γ: ['δ, ⊤], 'δ: [⊥, 'γ], 'ε: ['α, ⊤], *
> ⊢ (('ε ⊔ 'γ) → 'δ ⊓ 'β, 'α) → 'β
