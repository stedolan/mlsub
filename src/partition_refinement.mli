type t
val make : int -> t
val refine : t -> int list -> unit
val to_sets : t -> int list list
