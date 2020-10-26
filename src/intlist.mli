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

(* peel_max [k] [m] returns Some (v, m') if m = m', (k,v), or None if k is absent.
   Assumes that there is no key larger than k in m.  *)
val peel_max : 'k -> ('k, 'v) t -> ('v * ('k, 'v) t) option

(* FIXME: maybe make this less int-like? empty could be int t *)
val cons_max : (int, 'v) t -> int -> 'v -> (int, 'v) t


(* Add a constant to each key *)
val increase_keys : int -> ('k, 'v) t -> ('k, 'v) t


val iter : ('k, 'v) t -> ('k -> 'v -> unit) -> unit
val wf : ('k, 'v) t -> unit

val contains : ('k, 'v) t -> 'k -> bool

val to_list : ('k, 'v) t -> ('k * 'v) list


type ('k, 'a) take_max_result =
  | Empty
  | Cons of 'k * 'a * ('k, 'a) t
val take_max : ('k, 'a) t -> ('k, 'a) take_max_result

type ('k, 'a, 'b) take_max2_result =
  | Empty
  | Left of 'k * 'a * ('k, 'a) t
  | Right of 'k * 'b * ('k, 'b) t
  | Both of 'k * 'a * 'b * ('k, 'a) t * ('k, 'b) t
val take_max2 : ('k, 'a) t -> ('k, 'b) t -> ('k, 'a, 'b) take_max2_result

val as_singleton : ('k, 'a) t -> 'k * 'a
val is_singleton : ('k, 'a) t -> bool
