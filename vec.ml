type z = Z
type 'a s = S

module List = struct
  type 'a t = 'a list = [] | (::) of 'a * 'a list
  include List
end

type ('a, _) t =
| [] : ('a, z) t
| (::) : 'a * ('a, 'n) t -> ('a, 'n s) t

let cons x xs = x :: xs

type ('a, 'n) vector = ('a, 'n) t

let rec map : type n . ('a -> 'b) -> ('a, n) t -> ('b, n) t =
  fun f xs -> match xs with
  | [] -> []
  | x :: xs -> f x :: map f xs

let rec zip : type n . ('a, n) t -> ('b, n) t -> ('a * 'b, n) t =
  fun xs ys -> match xs, ys with
  | [], [] -> []
  | (x :: xs), (y :: ys) -> (x,y) :: zip xs ys

let rec unzip : type n . ('a * 'b, n) t -> ('a, n) t * ('b, n) t = function
  | [] -> [], []
  | (x,y) :: rest ->
     let xs, ys = unzip rest in
     (x :: xs), (y :: ys)

type (_, _) inc =
| Same : ('a, 'a) inc
| Inc : ('a, 'b) inc -> ('a, 'b s) inc

type ('a, 'b) cmp = Eq : ('a, 'a) cmp | NotEq : ('a, 'b) cmp

let rec cmp_inc : type n m1 m2 . (n, m1) inc -> (n, m2) inc -> (m1, m2) cmp =
  fun i1 i2 -> match i1, i2 with
  | Same, Same -> Eq
  | Same, Inc _ -> NotEq
  | Inc _, Same -> NotEq
  | Inc i1, Inc i2 -> 
     match cmp_inc i1 i2 with
     | Eq -> Eq
     | NotEq -> NotEq


type 'n num = (z, 'n) inc

let rec add : type a b c . (a, b) inc -> (b, c) inc -> (a, c) inc =
  fun x y -> match y with
  | Same -> x
  | Inc y' -> Inc (add x y')

let rec repeat : type n . n num -> 'a -> ('a, n) vector =
  fun n x -> match n with
  | Same -> []
  | Inc n -> x :: repeat n x

let rec take : type n m . (n, m) inc -> ('a, m) vector -> 'a list * ('a, n) vector =
  fun i xs -> match i with
  | Same -> [], xs
  | Inc i ->
     let x :: xs = xs in
     let (start, rest) = take i xs in
     x :: start, rest

let rec length : type n . ('a, n) t -> n num = function
  | [] -> Same
  | _ :: xs -> Inc (length xs)

type 'a vecn = Vecn : ('a, 'n) t -> 'a vecn [@@unboxed]
let rec of_list : 'a list -> 'a vecn = function
  | [] -> Vecn []
  | x :: xs ->
     let Vecn xs' = of_list xs in
     Vecn (x :: xs')

let as_length : type n . n num -> 'a vecn -> ('a, n) t option =
  fun n (Vecn v) -> match cmp_inc n (length v) with
  | NotEq -> None
  | Eq -> Some v

module Prefix = struct
  type (_,_,_) t =
    | [] : ('a, 'n, 'n) t
    | (::) : 'a * ('a, 'n, 'm) t -> ('a, 'n, 'm s) t

  let rec length : type n m . ('a, n, m) t -> (n, m) inc =
    function
    | [] -> Same
    | x :: xs -> Inc (length xs)

  let rec map : type n m . ('a -> 'b) -> ('a, n, m) t -> ('b, n, m) t =
    fun f xs -> match xs with
    | [] -> []
    | x :: xs -> f x :: map f xs

  let rec prepend : type n m . ('a, n, m) t -> ('a, n) vector -> ('a, m) vector =
    fun pre v -> match pre with
    | [] -> v
    | x :: xs -> x :: prepend xs v

  let rec to_list : type n m . ('a, n, m) t -> 'a list =
    function
    | [] -> []
    | x :: xs -> x :: to_list xs

  let rec zip : type n m . ('a, n, m) t -> ('b, m) vector -> ('a * 'b, n, m) t * ('b, n) vector =
    fun pre v -> match pre, v with
    | [], v -> [], v
    | x :: xs, y :: ys ->
       let (xys, tail) = zip xs ys in
       ((x,y) :: xys, tail)
end

module Zipper = struct
  type (_, _, _) t =
    | Nil : ('a, 'n, 'n) t
    | Snoc : ('a, 'n s, 'm) t * 'a -> ('a, 'n, 'm) t

  let rec prepend : type n m . ('a, n, m) t -> ('a, n) vector -> ('a, m) vector =
    fun pre v -> match pre with
    | Nil -> v
    | Snoc (xs, x) -> prepend xs (x :: v)

  let rec prepend_pfx : type n m r . ('a, n, r) t -> ('a, m, n) Prefix.t -> ('a, m, r) Prefix.t =
    fun z p -> match z with
    | Nil -> p
    | Snoc (xs, x) -> prepend_pfx xs (Prefix.(x :: p))

  let rec to_prefix z = prepend_pfx z Prefix.[]

end

let rec to_list : type n . ('a, n) t -> 'a list = function
  | [] -> List.[]
  | x :: xs -> List.(x :: to_list xs)
