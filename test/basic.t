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
