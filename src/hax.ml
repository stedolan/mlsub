module Sing : sig
  type +'a t = private 'a list
  val inj : 'a -> 'a t
  val prj : 'a t -> 'a
end = struct
  type 'a t = 'a list
  let inj x = [x]
  let prj = List.hd
end

type +'a box = { foo : 'a } 

let f x = (x : 'a Sing.t box :> 'a list box)
