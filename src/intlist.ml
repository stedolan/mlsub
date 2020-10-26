type ('k, +'v) t =
  | Empty
  | Cons : (int, 'v) t * int * 'v -> (int, 'v) t

let empty = Empty
let is_empty (type k) : (k, _) t -> bool = function Empty -> true | Cons _ -> false

let singleton k v = Cons (Empty, k, v)

let rec length : type k . (k, _) t -> int = function
  | Empty -> 0
  | Cons(m, _, _) -> length m + 1

let rec union : type k . (k -> 'v -> 'v -> 'v) -> (k, 'v) t -> (k, 'v) t -> (k, 'v) t =
  fun f a b -> match a, b with
  | Empty, x | x, Empty -> x
  | Cons(a, ka, va), Cons(b, kb, vb) when ka = kb ->
     Cons(union f a b, ka, f ka va vb)
  | Cons(a, ka, va), Cons(_, kb, _) when ka > kb ->
     Cons(union f a b, ka, va)
  | Cons(_, _ka, _), Cons(b, kb, vb) (* when _ka < kb *) ->
     Cons(union f a b, kb, vb)

let rec remove : type k . (k, 'v) t -> (k, 'a) t -> (k, 'v) t =
  fun a b -> match a, b with
  | Empty, _ -> Empty
  | a, Empty -> a
  | Cons(a, ka, _), Cons(b, kb, _) when ka = kb ->
     remove a b
  | Cons(a, ka, va), Cons(_, kb, _) when ka > kb ->
     Cons(remove a b, ka, va)
  | Cons(_, _ka, _), Cons(b, _kb, _) (* when _ka < kb *) ->
     remove a b

let add t k v = union (fun _ _a b -> b) t (singleton k v)
     

let rec map : type k . (k -> 'a -> 'b) -> (k, 'a) t -> (k, 'b) t =
  fun f m -> match m with
  | Empty -> Empty
  | Cons(m, k, v) -> Cons(map f m, k, f k v)

let rec filter : type k . (k -> 'a -> bool) -> (k, 'a) t -> (k, 'a) t =
  fun f m -> match m with
  | Empty -> Empty
  | Cons(m, k, v) when f k v -> Cons (filter f m, k, v)
  | Cons(m, _, _) -> filter f m

let rec union_map : type k a b c .
  left:(k -> a -> c) ->
  right:(k -> b -> c) ->
  both:(k -> a -> b -> c) ->
  (k, a) t -> (k, b) t -> (k, c) t =
  fun ~left ~right ~both a b -> match a, b with
  | Empty, x -> map right x
  | x, Empty -> map left x
  | Cons(a, ka, va), Cons(b, kb, vb) when ka = kb ->
     Cons(union_map ~left ~right ~both a b, ka, both ka va vb)
  | Cons(a, ka, va), Cons(_, kb, _) when ka > kb ->
     Cons(union_map ~left ~right ~both a b, ka, left ka va)
  | Cons(_, _ka, _), Cons(b, kb, vb) (* when _ka < kb *) ->
     Cons(union_map ~left ~right ~both a b, kb, right kb vb)

let is_supported (type k) (k : k) : (k, _) t -> bool = function
  | Empty -> true
  | Cons(_, k', _) -> k' <= k

let all_below (type k) (k : k) : (k, _) t -> bool = function
  | Empty -> true
  | Cons(_, k', _) -> k' < k

let peel_max (type k) (k : k) : (k, 'v) t -> ('v * (k, 'v) t) option = function
  | Cons(m', k', v) when k' = k -> Some (v, m')
  | _ -> None

let cons_max m k v =
  assert (all_below k m);
  Cons (m, k, v)


let rec increase_keys : type k . int -> (k, 'v) t -> (k, 'v) t =
  fun n m -> match m with
  | Empty -> Empty
  | Cons(m, ka, va) -> Cons (increase_keys n m, ka + n, va)


let rec iter : type k . (k, 'v) t -> (k -> 'v -> unit) -> unit =
  fun m f -> match m with
  | Empty -> ()
  | Cons(m, k, v) -> f k v; iter m f

let rec wf : type k . (k, 'v) t -> unit =
  function
  | Empty -> ()
  | Cons(Empty, _, _) -> ()
  | Cons(Cons(_, k1, _) as m, k2, _) ->
     assert (k1 < k2); wf m

let rec contains : type k . (k, 'v) t -> k -> bool =
  fun m k -> match m with
  | Empty -> false
  | Cons(_, k', _) when k' = k -> true
  | Cons(_, k', _) when k' < k -> false
  | Cons(m, _, _) -> contains m k

let rec to_list : type k . (k, 'v) t -> (k * 'v) list =
  function
  | Empty -> []
  | Cons(m, k, v) -> (k, v) :: to_list m

type ('k, 'a, 'b) take_max2_result =
  | Empty
  | Left of 'k * 'a * ('k, 'a) t
  | Right of 'k * 'b * ('k, 'b) t
  | Both of 'k * 'a * 'b * ('k, 'a) t * ('k, 'b) t

type ('k, 'a) take_max_result =
  | Empty
  | Cons of 'k * 'a * ('k, 'a) t
let take_max (type k) (a : (k, 'a) t) : (k, 'a) take_max_result =
  match a with
  | Empty -> Empty
  | Cons(a, ka, va) -> Cons (ka, va, a)

let take_max2 (type k) (a : (k, 'a) t) (b : (k, 'b) t) : (k, 'a, 'b) take_max2_result =
  match a, b with
  | Empty, Empty ->
     Empty
  | Cons(a, ka, va), Empty ->
     Left(ka, va, a)
  | Empty, Cons(b, kb, vb) ->
     Right(kb, vb, b)
  | Cons(a, ka, va), Cons(b, kb, vb) when ka = kb ->
     Both(ka, va, vb, a, b)
  | Cons(a, ka, va), Cons(b, kb, vb) ->
     if ka > kb then
       Left(ka, va, a)
     else
       Right(kb, vb, b)

let as_singleton (type k) : (k, 'a) t -> k * 'a = function
  | Cons(Empty, k, v) -> k, v
  | _ -> assert false

let is_singleton (type k) : (k, 'a) t -> bool = function
  | Cons(Empty, _, _) -> true
  | _ -> false
