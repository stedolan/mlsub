type ('k, +'v) t

val empty : ('k, 'v) t

val is_empty : ('k, 'v) t -> bool

val length : ('k, 'v) t -> int

val singleton : int -> 'v -> (int, 'v) t

val map : ('k -> 'a -> 'b) -> ('k, 'a) t -> ('k, 'b) t

val filter : ('k -> 'v -> bool) -> ('k, 'v) t -> ('k, 'v) t

val union : ('k -> 'v -> 'v -> 'v) -> ('k, 'v) t -> ('k, 'v) t -> ('k, 'v) t

val remove : ('k, 'a) t -> ('k, 'b) t -> ('k, 'a) t

val add : (int, 'v) t -> int -> 'v -> (int, 'v) t

val union_map :
  left:('k -> 'a -> 'c) ->
  right:('k -> 'b -> 'c) ->
  both:('k -> 'a -> 'b -> 'c) ->
  ('k, 'a) t -> ('k, 'b) t -> ('k, 'c) t

(* [is_supported k xs] if every key of xs is <= k *)
val is_supported : 'k -> ('k, 'v) t -> bool

(* [all_below k xs] if every key of xs is <k *)
val all_below : 'k -> ('k, 'v) t -> bool

(* Add a constant to each key *)
val increase_keys : int -> ('k, 'v) t -> ('k, 'v) t


val iter : ('k, 'v) t -> ('k -> 'v -> unit) -> unit
val wf : ('k, 'v) t -> unit

val contains : ('k, 'v) t -> 'k -> bool

val to_list : ('k, 'v) t -> ('k * 'v) list

val as_singleton : ('k, 'a) t -> 'k * 'a
val is_singleton : ('k, 'a) t -> bool
