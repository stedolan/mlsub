type 'a t

val create : unit -> 'a t

val length : 'a t -> int
val push : 'a t -> 'a -> int
(* raises Invalid_argument if >= length *)
val get : 'a t -> int -> 'a

val iter : 'a t -> ('a -> unit) -> unit
val iteri : 'a t -> (int -> 'a -> unit) -> unit
