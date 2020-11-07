let f = fn (x) { x, x }; f
> let f = fn (x) { <err> }; f
> typechecking error: Failure("bad exp")

let x = 1; (let y = 2 2; {x,y})
> let x = 1; (<err>)
> typechecking error: Failure("bad exp")

fn (id : [A]. A -> A) { id(42) }
> fn (<err>) { id(42) }
> typechecking error: Failure("bad pat")

fn(x, y, ~k: int) { (x:int,k,y) }
> fn (x, y, ~k : int) { (<err>) }
> typechecking error: Failure("bad exp")


fn (x)
> parser failure: bad parse
