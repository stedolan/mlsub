(* Borrowed from the OCaml standard library, modified to fit a silly
   syntax.  Functions that use unsupported features (e.g. multiple
   simultaneous matches, arithmetic, arrays) commented out.

   Try uncommenting functions using records (e.g. "partition"). They
   won't work with OCaml, though. *)


let rec length_aux = fun len -> fun x -> match x with
    [] -> len
  | a::l -> length_aux (len + 1) l

let length = fun l -> length_aux 0 l

let hd = fun x -> match x with
    [] -> assert false
  | a::l -> a

let tl = fun x -> match x with
    [] -> assert false
  | a::l -> l


let nth = fun l -> fun n ->
  if n < 0 then assert false else
  let rec nth_aux = fun l -> fun n ->
    match l with
      [] -> assert false
    | a::l -> if n = 0 then a else nth_aux l (n-1)
  in nth_aux l n


(* from pervasives.ml *)
let rec append = fun l1 -> fun l2 ->
  match l1 with
    [] -> l2
  | hd :: tl -> hd :: (append tl l2)

let rec rev_append = fun l1 -> fun l2 ->
  match l1 with
    [] -> l2
  | a :: l -> rev_append l (a :: l2)

let rev = fun l -> rev_append l []

let rec flatten = fun x -> match x with
    [] -> []
  | l::r -> append l (flatten r)

let concat = flatten

let rec map = fun f -> fun x -> match x with
    [] -> []
  | a::l -> let r = f a in r :: map f l

let rec mapi = fun i -> fun f -> fun x -> match x with
    [] -> []
  | a::l -> let r = f i a in r :: mapi (i + 1) f l

let mapi = fun f -> fun l -> mapi 0 f l

let rev_map = fun f -> fun l ->
  let rec rmap_f = fun accu -> fun x -> match x with
      [] -> accu
    | a::l -> rmap_f (f a :: accu) l
  in
  rmap_f [] l


let rec iter = fun f -> fun x -> match x with
    [] -> ()
  | a::l -> let unused = f a in iter f l

let rec iteri = fun i -> fun f -> fun x -> match x with
    [] -> ()
  | a::l -> let _ = f i a in iteri (i + 1) f l

let iteri = fun f -> fun l -> iteri 0 f l


let rec fold_left = fun f -> fun accu -> fun l ->
  match l with
    [] -> accu
  | a::l -> fold_left f (f accu a) l

let rec fold_right = fun f -> fun l -> fun accu ->
  match l with
    [] -> accu
  | a::l -> f a (fold_right f l accu)


let rec map2 = fun f -> fun l1 -> fun l2 -> 
   match l1 with
    [] ->
     (match l2 with
        [] -> []
      | a2 :: l2 -> assert false)
  | a1 :: l1 ->
     (match l2 with
        [] -> assert false
      | a2 :: l2 -> let r = f a1 a2 in r :: map2 f l1 l2)

let rev_map2 = fun f -> fun l1 -> fun l2 ->
  let rec rmap2_f = fun accu -> fun l1 -> fun l2 ->
    match l1 with
      [] ->
       (match l2 with
          [] -> accu
        | a2 :: l2 -> assert false)
    | a1 :: l1 ->
       (match l2 with
          [] -> assert false
        | a2 :: l2 -> rmap2_f (f a1 a2 :: accu) l1 l2)
  in
  rmap2_f [] l1 l2

(*
let rec iter2 f l1 l2 =
  match (l1, l2) with
    ([], []) -> ()
  | (a1::l1, a2::l2) -> f a1 a2; iter2 f l1 l2
  | (_, _) -> invalid_arg "List.iter2"

let rec fold_left2 f accu l1 l2 =
  match (l1, l2) with
    ([], []) -> accu
  | (a1::l1, a2::l2) -> fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) -> invalid_arg "List.fold_left2"

let rec fold_right2 f l1 l2 accu =
  match (l1, l2) with
    ([], []) -> accu
  | (a1::l1, a2::l2) -> f a1 a2 (fold_right2 f l1 l2 accu)
  | (_, _) -> invalid_arg "List.fold_right2"
 *)

let rec for_all = fun p -> fun x -> match x with
    [] -> true
  | a::l -> if p a then for_all p l else false

let rec exists = fun p -> fun x -> match x with
    [] -> false
  | a::l -> if p a then true else exists p l
(*
let rec for_all2 p l1 l2 =
  match (l1, l2) with
    ([], []) -> true
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> invalid_arg "List.for_all2"

let rec exists2 p l1 l2 =
  match (l1, l2) with
    ([], []) -> false
  | (a1::l1, a2::l2) -> p a1 a2 || exists2 p l1 l2
  | (_, _) -> invalid_arg "List.exists2"

let rec mem x = function
    [] -> false
  | a::l -> compare a x = 0 || mem x l

let rec memq x = function
    [] -> false
  | a::l -> a == x || memq x l
 *)

(*
let rec assoc = fun x -> fun l -> match l with
    [] -> assert false
  | p::l -> if p.fst = x then p.snd else assoc x l
*)

(*
let rec assq x = function
    [] -> raise Not_found
  | (a,b)::l -> if a == x then b else assq x l

let rec mem_assoc x = function
  | [] -> false
  | (a, b) :: l -> compare a x = 0 || mem_assoc x l

let rec mem_assq x = function
  | [] -> false
  | (a, b) :: l -> a == x || mem_assq x l
 *)

(*
let rec remove_assoc = fun x -> fun l -> match l with
    [] -> []
  | pair :: l ->
      if pair.fst = x then l else pair :: remove_assoc x l


*)

(*
let rec remove_assq x = function
  | [] -> []
  | (a, b as pair) :: l -> if a == x then l else pair :: remove_assq x l

let rec find p = function
  | [] -> raise Not_found
  | x :: l -> if p x then x else find p l

let find_all p =
  let rec find accu = function
  | [] -> rev accu
  | x :: l -> if p x then find (x :: accu) l else find accu l in
  find []

let filter = find_all
 *)

(*
let partition = fun p -> fun l ->
  let rec part = fun yes -> fun no -> fun l -> match l with
    [] -> { yes = rev yes; no = rev no }
  | x :: l -> if p x then part (x :: yes) no l else part yes (x :: no) l in
  part [] [] l
*)

(*
let rec split = function
    [] -> ([], [])
  | (x,y)::l ->
      let (rx, ry) = split l in (x::rx, y::ry)

let rec combine l1 l2 =
  match (l1, l2) with
    ([], []) -> []
  | (a1::l1, a2::l2) -> (a1, a2) :: combine l1 l2
  | (_, _) -> invalid_arg "List.combine"

              *)

(** sorting *)
(*
let rec merge cmp l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      if cmp h1 h2 <= 0
      then h1 :: merge cmp t1 l2
      else h2 :: merge cmp l1 t2
;;

let rec chop k l =
  if k = 0 then l else begin
    match l with
    | x::t -> chop (k-1) t
    | _ -> assert false
  end
;;

let stable_sort cmp l =
  let rec rev_merge l1 l2 accu =
    match l1, l2 with
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        if cmp h1 h2 <= 0
        then rev_merge t1 l2 (h1::accu)
        else rev_merge l1 t2 (h2::accu)
  in
  let rec rev_merge_rev l1 l2 accu =
    match l1, l2 with
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        if cmp h1 h2 > 0
        then rev_merge_rev t1 l2 (h1::accu)
        else rev_merge_rev l1 t2 (h2::accu)
  in
  let rec sort n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       if cmp x1 x2 <= 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       if cmp x1 x2 <= 0 then begin
         if cmp x2 x3 <= 0 then [x1; x2; x3]
         else if cmp x1 x3 <= 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         if cmp x1 x3 <= 0 then [x2; x1; x3]
         else if cmp x2 x3 <= 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n asr 1 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = rev_sort n1 l in
       let s2 = rev_sort n2 l2 in
       rev_merge_rev s1 s2 []
  and rev_sort n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       if cmp x1 x2 > 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       if cmp x1 x2 > 0 then begin
         if cmp x2 x3 > 0 then [x1; x2; x3]
         else if cmp x1 x3 > 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         if cmp x1 x3 > 0 then [x2; x1; x3]
         else if cmp x2 x3 > 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n asr 1 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = sort n1 l in
       let s2 = sort n2 l2 in
       rev_merge s1 s2 []
  in
  let len = length l in
  if len < 2 then l else sort len l
;;

let sort = stable_sort;;
let fast_sort = stable_sort;;
 *)
(* Note: on a list of length between about 100000 (depending on the minor
   heap size and the type of the list) and Sys.max_array_size, it is
   actually faster to use the following, but it might also use more memory
   because the argument list cannot be deallocated incrementally.

   Also, there seems to be a bug in this code or in the
   implementation of obj_truncate.

external obj_truncate : 'a array -> int -> unit = "caml_obj_truncate"

let array_to_list_in_place a =
  let l = Array.length a in
  let rec loop accu n p =
    if p <= 0 then accu else begin
      if p = n then begin
        obj_truncate a p;
        loop (a.(p-1) :: accu) (n-1000) (p-1)
      end else begin
        loop (a.(p-1) :: accu) n (p-1)
      end
    end
  in
  loop [] (l-1000) l
;;

let stable_sort cmp l =
  let a = Array.of_list l in
  Array.stable_sort cmp a;
  array_to_list_in_place a
;;
*)


(** sorting + removing duplicates *)
(*
let sort_uniq cmp l =
  let rec rev_merge l1 l2 accu =
    match l1, l2 with
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        let c = cmp h1 h2 in
        if c = 0 then rev_merge t1 t2 (h1::accu)
        else if c < 0
        then rev_merge t1 l2 (h1::accu)
        else rev_merge l1 t2 (h2::accu)
  in
  let rec rev_merge_rev l1 l2 accu =
    match l1, l2 with
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        let c = cmp h1 h2 in
        if c = 0 then rev_merge_rev t1 t2 (h1::accu)
        else if c > 0
        then rev_merge_rev t1 l2 (h1::accu)
        else rev_merge_rev l1 t2 (h2::accu)
  in
  let rec sort n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then [x1]
       else if c < 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x2]
         else if c < 0 then [x2; x3] else [x3; x2]
       end else if c < 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x1; x2]
         else if c < 0 then [x1; x2; x3]
         else let c = cmp x1 x3 in
         if c = 0 then [x1; x2]
         else if c < 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         let c = cmp x1 x3 in
         if c = 0 then [x2; x1]
         else if c < 0 then [x2; x1; x3]
         else let c = cmp x2 x3 in
         if c = 0 then [x2; x1]
         else if c < 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n asr 1 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = rev_sort n1 l in
       let s2 = rev_sort n2 l2 in
       rev_merge_rev s1 s2 []
  and rev_sort n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then [x1]
       else if c > 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x2]
         else if c > 0 then [x2; x3] else [x3; x2]
       end else if c > 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x1; x2]
         else if c > 0 then [x1; x2; x3]
         else let c = cmp x1 x3 in
         if c = 0 then [x1; x2]
         else if c > 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         let c = cmp x1 x3 in
         if c = 0 then [x2; x1]
         else if c > 0 then [x2; x1; x3]
         else let c = cmp x2 x3 in
         if c = 0 then [x2; x1]
         else if c > 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n asr 1 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = sort n1 l in
       let s2 = sort n2 l2 in
       rev_merge s1 s2 []
  in
  let len = length l in
  if len < 2 then l else sort len l
;;
 *)
