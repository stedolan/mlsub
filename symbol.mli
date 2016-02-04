type t
module Map : Map.S with type key = t
val intern : string -> t
val to_string : t -> string
val hash : t -> int
val fresh : string -> t

(* FIXME: tighten interface *)
module Dictionary : sig
  type symbol = t
  type hash_params = int * int
  val prob_collision_free : int -> int -> float -> float
  val pow2 : int -> int
  val estimate_size : int -> float -> int
  val shift : int -> int
  val check_for_duplicates : 'a array -> unit
  val pos : symbol -> int -> int -> int
  val try_hashtable_size : t array -> int -> (int * int * int) option
  val find_hashtable : int array -> int * int * int
  type 'a t = hash_params * 'a option array
  val generate : (symbol * 'a) list -> 'a t
end
