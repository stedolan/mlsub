This is a prototype type inferencer for an ML-like language with
subtyping and polymorphism. It's written in OCaml, and building it
requires Menhir.

It accepts lines containing programs written in a very limited subset
of OCaml (just lambdas, unit and `let`), and spews some debugging
output and their principal type if it likes them, and an unceremonious
exception if it does not.

Some examples, and their inferred types:

The identity function is given type `v0 -> v0`. All free variables in
inferred types are considered universally quantified, as is the
custom in these parts.

    fun x -> x
    (v0 -> v0)

The inferencer actually spits out two types: the original and a
simplified one. The second one is a simplified but equivalent
rendering of the first. The simplifier is not currently very good.

Type ascriptions can be used, and check polymorphic subsumption:

    (fun x -> x : a -> a)
    (v0 -> v0)

The ascription may be less general than the inferred type:

    (fun x -> x : unit -> unit)
    (unit -> unit)

But the inferencer won't like a more general or unrelated type:

    (fun x -> x : a -> b)
    <error>

On to something more interesting. Self-application can be typed in
this system:

    fun x -> x x
    (((v1 -> v0) & v1) -> v0)

The argument `x` must be both a `v1 -> v0` and a `v1`. One thing you
can do with the self-application function is apply it to itself (why
you would do this is outside the scope of this work):

    (fun x -> x x) (fun x -> x x)
    Bot

This is the bottom type, equivalent to just `a` (universally
quantified). We can check this with a type ascription:

    ((fun x -> x x) (fun x -> x x) : a)
    Bot

The Y combinator can be typed by this system (here showing the
simplified type, the first attempt is a bit uglier):

    (fun f -> (fun x -> f (x x)) (fun x -> f (x x)))
    ((v0 -> v0) -> v0)

This version of the Y combinator doesn't work in strict languages. The
CBV-safe version eta-expands, giving:

    (fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v)))
    (((v1 -> v0) -> ((v1 -> v0) & v2)) -> v2)

This is slightly different from the expected `((a -> b) -> (a -> b))
-> (a -> b)`. An ascription check shows that it is more general:

    (fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v)) :
      ((a -> b) -> (a -> b)) -> (a -> b))
    (((v1 -> v0) -> (v1 -> v0)) -> (v1 -> v0))

The extra generality comes from allowing `v2` to be more general than
`v1 -> v0`, which comes into play if `->` has subtypes.

We can use fixpoint combinators to make values with recursive types,
such as a function that takes arbitrarily many arguments:

    (fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v))) 
       (fun f -> fun x -> f)
    (Top -> rec v0 = (Top -> v0))

This type could be folded into the simpler `rec a = Top -> a`; but the
(rather stupid) simplifier can't figure that out yet.
