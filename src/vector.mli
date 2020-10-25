type 'a t

val create : unit -> 'a t

val length : 'a t -> int
val push : 'a t -> 'a -> int
(* raises Invalid_argument if >= length *)
val get : 'a t -> int -> 'a

val to_array : 'a t -> 'a array
val of_array : 'a array -> 'a t

val clear : 'a t -> unit

val iter : 'a t -> ('a -> unit) -> unit
val iteri : 'a t -> (int -> 'a -> unit) -> unit

val fold_lefti : ('a -> int -> 'b -> 'a) -> 'a -> 'b t -> 'a
