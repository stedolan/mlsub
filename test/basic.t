# FIXME: currently using internal syntax (Typedefs.pr_*)

#
# Literals
#

0
> int

5
> int

true
> bool

false
> bool

# FIXME: string syntax
# FIXME: interesting numeric literals (negative, hex, float, etc.)

# checking forms

(42 : int)
> int

(true : bool)
> bool

(42 : string)
> typechecking error: Failure("incompat")

#
# If
#

if (true) { 1 } else { 2 }
> int

if (false) { 1 } else { false }
> ⊤

#
# Tuples
#

(1, 2)
> (int, int)

(true, 3, 4)
> (bool, int, int)

# python-style singleton tuples
(4,)
> (int)

(.foo=1)
> (foo: int)

(.foo=1,)
> (foo: int)

# not a singleton tuple
(1)
> int

# allowed but weird (trailing comma in an empty tuple)
(,)
> ()

# arity
((1,),(2,3),(4,5,6),(7,8,9,10))
> ((int), (int, int), (int, int, int), (int, int, int, int))

# empty tuple (unit type)
()
> ()

# named fields
((.foo=20, .bar=17), (.baz=1))
> ((foo: int, bar: int), (baz: int))

# mixture of named and unnamed
(1, 2, .bar=3, .baz=true)
> (int, int, bar: int, baz: bool)

# joins
if (true) { (1, 2) } else { (1, true, 3) }
> (int, ⊤, ...)

if (false) { (.foo=1,.bar=2) } else { (.foo=1,.baz=()) }
> (foo: int, ...)

true.foo
> typechecking error: Failure("incompat")

@bot
> ⊥

# checking join of functions and meet of records
if true { (@bot : (.foo:(int,int), .bar:any) -> string) } else { (@bot : (.foo:(int,int), .bar:any) -> string) }
> (foo: (int, int), bar: ⊤) → string

if true { (@bot : ((int,any), .foo:(int,int), .bar:any) -> string) } else {(@bot : ((any,string), .bar:string, .foo:(string,any)) -> nothing)}
> ((int, string), foo: (⊥, int), bar: string) → string



#
# Bidirectional typing. @true and @false have only checking forms.
#

@true
> typechecking error: Failure("pragma: true")

(@true : bool)
> bool

((@true, @false) : (bool, bool))
> (bool, bool)

((1, 2) : (int, int, int))
> typechecking error: Failure("missing positional field")

((1, 2, 3) : (int, int))
> typechecking error: Failure("too many positional fields. FIXME open tuples")

# weird. Should I allow this? eta-expansion?
(1, 2, ...)
> (int, int, ...)

((1, 2) : (int, int, ...))
> (int, int, ...)

# ((1, 2, 3) : (int, int, ...)) ???
