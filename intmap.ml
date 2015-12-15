(*
type ('a, _) map =
| Empty : ('a, [> `Empty]) map
| Leaf : int * 'a -> ('a, [> `Nonempty]) map
| Branch : int * ('a, [`Nonempty]) map * ('a, [`Nonempty]) map -> ('a, [> `Nonempty]) map

type 'a t = ('a, [`Nonempty | `Empty]) map

type 'a nmap = ('a, [`Nonempty]) map

let empty = Empty

let is_empty = function
  | Empty -> true
  | _ -> false


let branchbit p = 
  (* lowest 1 bit of p *)
  p land (-p)

let rec mem_nonempty (map : ('a, [> `Nonempty]) map) key = match map with
  | Leaf (key', value') -> key = key'
  | Branch (p, t0, t1) ->
    mem_nonempty (if key land (branchbit p) == 0 then t0 else t1) key

let mem map key = match map with
  | Empty -> false
  | Leaf _ -> mem_nonempty map key
  | Branch _ -> mem_nonempty map key


let rec mem (map : 'a nmap) key = match map with
  | Leaf (key', value') -> key = key'
  | Branch (p, t0, t1) ->
    mem (if key land (branchbit p) == 0 then t0 else t1) key
 *)


(*
type 'a t =
| Branch of int * 'a t * 'a t
| Leaf of int * 'a



let get_prefix = function
  | Leaf (p, x) -> p
  | Branch (p, t0, t1) -> p

let branchbit p = 
  (* lowest 1 bit of p *)
  p land (-p)

let rec verify_nonempty t =
  match t with
  | Leaf (p, x) -> ()
  | Branch (0, _, _) -> assert false
  | Branch (pfx, t0, t1) ->
    let pfx' = get_prefix t in
    let br = branchbit pfx' in
    let hmask = -br lxor br in
    let p0 = get_prefix t0 in
    let p1 = get_prefix t1 in
    assert (pfx == pfx');
    assert (p0 land br == 0);
    assert (p0 land hmask == pfx land hmask);
    assert (p1 land br != 0);
    assert (p1 land hmask == pfx land hmask);
    verify_nonempty t0; verify_nonempty t1

let verify = function
  | Branch (0, _, _) -> ()
  | x -> verify_nonempty x

let v x = verify x; x



let rec empty = Branch (0, empty, empty)

let is_empty = function
  | Branch (0, _, _) -> true
  | _ -> false

let singleton key value =
  Leaf (key, value)



let branch_nonempty pfx a b =
  match a, b with
  | Branch (0, _, _), b -> b
  | a, Branch (0, _, _) -> a
  | a, b -> Branch (pfx, a, b)

let rec mem map key = match map with 
  | Branch (0, _, _) -> false
  | Leaf (key', value') -> key' = key
  | Branch (p, t0, t1) ->
    mem (if key land (branchbit p) == 0 then t0 else t1) key

let rec remove map key = match map with
  | Branch (0, _, _) -> empty
  | Leaf (key', value') when key' = key -> empty
  | Leaf (key', value') -> map
  | Branch (p, t0, t1) ->
    if key land (branchbit p) == 0 then
      Branch (p, remove t0 key, t1)
    else
      Branch (p, t0, remove t1 key)

let rec get map key = match map with
  | Branch (0, _, _) -> raise Not_found
  | Leaf (key', value') when key' = key -> value'
  | Leaf (key, value) -> raise Not_found
  | Branch (p, t0, t1) ->
    if key land (branchbit p) == 0 then
      get t0 key
    else 
      get t1 key

let () =
  match Sys.word_size with 32 | 64 -> () | _ -> failwith "Unsupported word size"

let high_bits_mask n =
  let n = n lor (n lsr 1) in
  let n = n lor (n lsr 2) in
  let n = n lor (n lsr 4) in
  let n = n lor (n lsr 8) in 
  let n = n lor (n lsr 16) in
  match Sys.word_size with
  | 32 -> n
  | 64 -> n lor (n lsr 32)
  | _ -> -1


(*
let rec index_of_first_eq arr i j mask v =
  if i == j then i
  else if arr.(i) land mask == v then i
  else index_of_first_eq arr (i+1) j mask v


let rec bitmap_of_subarray arr i j pfx b0 b1 =
  if i == j then Bitmap (pfx, b0, b1)
  else    
    let n = arr.(i) land bitmap_mask in
    if is_on_word_boundary n then
      bitmap_of_subarray arr (i+1) j (pfx lor boundary_pfxbits n) b0 b1
    else if n < word_size then
      bitmap_of_subarray arr (i+1) j pfx (b0 lor (1 lsl n)) b1
    else
      bitmap_of_subarray arr (i+1) j pfx b0 (b1 lor (1 lsl (n - word_size)))

let rec of_sorted_subarray arr i j = (* half open [i,j) *)
  let low = arr.(i) and high = arr.(j-1) in
  if low land (lnot bitmap_mask) == high land (lnot bitmap_mask) then
    (* create a bitmap node *)
    let pfx = (low land (lnot bitmap_mask)) lor bitmap_branchbit in
    bitmap_of_subarray arr i j pfx 0 0
  else
    (* create a branch node *)
    let m = high_bits_mask (low lxor high) in
    let br = m lxor (m lsr 1) in
    let pfx = (arr.(i) land (lnot m)) lor br in
    if br == min_int then
      (* branching on the sign bit *)
      let k = index_of_first_eq arr i j br 0 in
      Branch (pfx, of_sorted_subarray arr k j, of_sorted_subarray arr i k)
    else
      let k = index_of_first_eq arr i j br br in
      Branch (pfx, of_sorted_subarray arr i k, of_sorted_subarray arr k j)

let of_sorted_array arr =
  let len = Array.length arr in
  if len == 0 then empty else of_sorted_subarray arr 0 len


unionL : aL -> bL -> aR -> bR -> T

*)

(* Left and right folds *)
  
let rec fold_left_nonempty f acc = function
  | Leaf (p, x) -> f acc p x
  | Branch (p, t0, t1) ->
    fold_left_nonempty f (fold_left_nonempty f acc t0) t1

let fold_left f acc = function
  | Branch (0, _, _) -> acc
  | Leaf (p, x) -> f acc p x
  | Branch (p, t0, t1) when p = min_int ->
    (* the data structure treats ints as unsigned.
       to generate correctly-sorted output, we special-case 
       branching on the sign bit *)
    fold_left_nonempty f (fold_left_nonempty f acc t1) t0
  | Branch (p, t0, t1) ->
    fold_left_nonempty f (fold_left_nonempty f acc t0) t1

let rec fold_right_nonempty f map acc = match map with
  | Leaf (p, x) -> f p x acc
  | Branch (p, t0, t1) ->
    fold_right_nonempty f t0 (fold_right_nonempty f t1 acc)

let fold_right f map acc = match map with
  | Branch (0, _, _) -> acc
  | Leaf (p, x) -> f p x acc
  | Branch (p, t0, t1) when p = min_int ->
    (* the data structure treats ints as unsigned.
       to generate correctly-sorted output, we special-case 
       branching on the sign bit *)
    fold_right_nonempty f t1 (fold_right_nonempty f t0 acc)
  | Branch (p, t0, t1) ->
    fold_right_nonempty f t0 (fold_right_nonempty f t1 acc)
    
    


let to_assoc_list set = fold_right (fun i x l -> (i, x) :: l) set []
let iter set f = fold_left (fun _ n -> f n) () set

(* Union *)

let eqmask m a b = 
  a land m == b land m

let mk_branch diff pa a b =
  try
  verify a; verify b;
  let m = high_bits_mask diff in
  let br = m lxor (m lsr 1) in
  let pfx = (pa land (lnot m)) lor br in
  if pa land br == 0 then
    v (Branch (pfx, a, b))
  else
    v (Branch (pfx, b, a))
  with Not_found -> assert false


(*
let rec union_nonempty pa bra ma a pb brb mb b =
  let mshort = ma land mb in
  if pa land mshort <> pb land mshort then
    (* prefixes incompatible *)
    
  else if ma == mb then
    (* prefixes are the same *)
    match a, b with
    | Branch (_, a0, a1), Branch (_, b0, b1) when pa == pb -> 
      Branch (pa, union_nonempty a0 b0, union_nonempty a1 b1)
    | Leaf _, Leaf _ when pa == pb -> a
  else if mshort == ma then
    (* A has a shorter prefix *)
    match a with
    | Branch (_, a0, a1) ->
      if pb land bra == 0 then
        Branch (pa, union_nonempty a0 b, a1)
      else
        Branch (pa, a0, union_nonempty a1 b)
    | _ -> assert false
  else
    (* B has a shorter prefix *)
    match b with
    | Branch (_, b0, b1) ->
      if pa land brb == 0 then
        Branch (pb, union_nonempty a b0, b1)
      else
        Branch (pb, b0, union_nonempty a b1)

    


let rec union_nonempty a b =
  let pa = get_prefix a and pb = get_prefix b in
  let npa = -pa and npb = -pb in
  let bra = pa land npa and brb = pb land npb in
  let ma = pa lxor npa and mb = pb lxor npb in
  let mshort = ma land mb in
  match a, b with
  | Leaf _, Leaf _ when pa = pb -> a
  | Branch (_, a0, a1), Branch (_, b0, b1) 
    when eqmask mshort pa pb ->
*)    

let rec union_nonempty a b =
  verify a; verify b;
  let pa = get_prefix a and pb = get_prefix b in
  let npa = -pa and npb = -pb in
  let bra = pa land npa and brb = pb land npb in
  let ma = pa lxor npa and mb = pb lxor npb in
  Printf.printf "%016x %016x %016x %016x\n" pa pb ma mb;
  match a, eqmask ma pa pb, b, eqmask mb pa pb with
  | Leaf (_, xa), _, Leaf (_, xb), _ when pa = pb -> Printf.printf "LL\n"; a
  | Branch (_, a0, a1), true, Branch (_, b0, b1), true ->
    assert (pa == pb);
    let a = v (union_nonempty a0 b0) and b = v (union_nonempty a1 b1) in
    (try v (Branch (pa, a, b)) with Not_found -> assert false)
  | Branch (_, a0, a1), true, _, _ ->
    if pb land bra == 0
    then Branch (pa, union_nonempty a0 b, a1)
    else Branch (pa, a0, union_nonempty a1 b)
  | _, _, Branch (_, b0, b1), true ->
    if pa land brb == 0
    then Branch (pb, union_nonempty a b0, b1)
    else Branch (pb, b0, union_nonempty a b1)
  | _, _, _, _ ->
    Printf.printf "B!\n"; 
    try v (mk_branch (pa lxor pb) pa a b) with Not_found -> assert false

let union a b = match a, b with
  | (Branch (0, _, _), x | x, Branch (0, _, _)) -> x
  | _, _ -> union_nonempty a b



let rec union_with_nonempty f a b =
  assert (not (is_empty a));
  assert (not (is_empty b));
  let pa = get_prefix a and pb = get_prefix b in
  let npa = -pa and npb = -pb in
  let bra = pa land npa and brb = pb land npb in
  let ma = pa lxor npa and mb = pb lxor npb in
  match a, eqmask ma pa pb, b, eqmask mb pa pb with
  | Leaf (_, xa), _, Leaf (_, xb), _ when pa = pb -> Leaf (pa, f xa xb)
  | Branch (_, a0, a1), true, Branch (_, b0, b1), true ->
    Branch (pa, union_with_nonempty f a0 b0, union_with_nonempty f a1 b1)
  | Branch (_, a0, a1), true, _, _ ->
    if pb land bra == 0
    then Branch (pa, union_with_nonempty f a0 b, a1)
    else Branch (pa, a0, union_with_nonempty f a1 b)
  | _, _, Branch (_, b0, b1), true ->
    if pa land brb == 0
    then Branch (pb, union_with_nonempty f a b0, b1)
    else Branch (pb, b0, union_with_nonempty f a b1)
  | _, _, _, _ ->
    mk_branch (pa lxor pb) pa a b

let union_with f a b = 
  verify a;
  verify b;
  match a, b with
  | (Branch (0, _, _), x | x, Branch (0, _, _)) -> x
  | _, _ -> union_with_nonempty f a b





let rec intersection_nonempty a b =
  let pa = get_prefix a and pb = get_prefix b in
  let ma = pa lxor (-pa) and mb = pb lxor (-pb) in
  let pdiff = pa lxor pb in
  match a, b with
  | Leaf (_, xa), Leaf (_, xb) when pa = pb -> a
  | Branch (_, a0, a1), _ when ma land pdiff = 0 ->
    (match b with 
    | Branch (_, b0, b1) when pa = pb ->
      branch_nonempty pa (intersection_nonempty a0 b0) (intersection_nonempty a1 b1)
    | _ -> if pb land pa = pa
      then intersection_nonempty a1 b
      else intersection_nonempty a0 b)
  | _, Branch (_, b0, b1) when mb land pdiff = 0 ->
    if pa land pb = pb
    then intersection_nonempty a b1
    else intersection_nonempty a b0
  | _, _ -> empty

let inter a b = match a, b with
  | Branch (0, _, _), x -> empty
  | x, Branch (0, _, _) -> empty
  | _, _ -> intersection_nonempty a b



let rec diff_nonempty a b =
  let pa = get_prefix a and pb = get_prefix b in
  let ma = pa lxor (-pa) and mb = pb lxor (-pb) in
  let pdiff = pa lxor pb in
  match a, b with
  | Leaf (_, xa), Leaf (_, xb) when pa = pb -> empty
  | Branch (_, a0, a1), _ when ma land pdiff = 0 ->
    (match b with 
    | Branch (_, b0, b1) when pa = pb ->
      branch_nonempty pa (diff_nonempty a0 b0) (diff_nonempty a1 b1)
    | _ -> if pb land pa = pa
      then Branch (pa, a0, diff_nonempty a1 b)
      else Branch (pa, diff_nonempty a0 b, a1))
  | _, Branch (_, b0, b1) when mb land pdiff = 0 ->
    if pa land pb = pb
    then diff_nonempty a b1
    else diff_nonempty a b0
  | _, _ -> a

let diff a b = match a, b with
  | (Branch (0, _, _), _) | (_, Branch (0, _, _)) -> a
  | _, _ -> diff_nonempty a b




 *)
module type IdentType = sig
  type t
  val get_id : t -> int
end

module type S = sig
  type t
  type elt
  val empty : t
  val singleton : elt -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val fold_left : t -> 'a -> ('a -> elt -> 'a) -> 'a
  val iter : t -> (elt -> unit) -> unit
  val is_empty : t -> bool
  val length : t -> int

  val mem : t -> elt -> bool
  val add : t -> elt -> t

  val of_list : elt list -> t
  val to_list : t -> elt list

  val subset : t -> t -> bool
  val min_elt : t -> elt

  val compare : t -> t -> int
end


module Fake (T : IdentType) : S with type elt = T.t = struct
  module M = Set.Make (struct type t = T.t let compare x y = compare (T.get_id x) (T.get_id y) end)
  type t = M.t
  type elt = T.t
  let empty = M.empty
  let singleton x = M.singleton x
  let inter = M.inter
  let union = M.union
  let diff = M.diff
  let iter a f = M.iter f a
  let fold_left a acc f = M.fold (fun x y -> f y x) a acc
  let is_empty = M.is_empty
  let length = M.cardinal
  let mem a x = M.mem x a
  let add a x = M.add x a
  let of_list xs = List.fold_left add empty xs
  let to_list = M.elements
  let subset = M.subset
  let min_elt = M.min_elt

  let compare = M.compare
end



(*                                                        
type 'a intmap = 'a t

module Make (T : IdentType) : S with type elt = T.t = struct
  type t = T.t intmap
  type elt = T.t
  let empty = empty
  let singleton x = singleton (T.get_id x) x
  let inter a b = inter a b
  let union (a : t) (b : t) : t = union a b
  let diff a b = diff a b
  let iter a f = verify a; fold_left (fun _ _ x -> f x) () a
  let fold_left a acc f = fold_left (fun a _ x -> f a x) acc a

  let is_empty = is_empty
  let length a = fold_left a 0 (fun n s -> n + 1)

  let mem a x = mem a (T.get_id x)
  let add a x = union a (singleton x)
  let of_list xs = List.fold_left add empty xs
  let to_list a = fold_right (fun i x l -> x :: l) a []
  let subset a b = (inter a b = a)
  let min_elt a = assert false
end


(*



let cmp_no_info = 3
and cmp_a_not_sub = 2
and cmp_b_not_sub = 1
and cmp_incomparable = 0

type comparison = 
| Subset
| Superset
| Equal
| Incomparable

let comparison_of_cmp_info = function
  | 3 -> Equal
  | 2 -> Superset
  | 1 -> Subset
  | 0 -> Incomparable
  | _ -> assert false

let int_of_bool (b : bool) : int = 
  Obj.magic b

let _ =
  assert (int_of_bool false == 0);
  assert (int_of_bool true == 1)


let cmpint a b ab =
  let n = int_of_bool (b == ab) in n + n + int_of_bool (a == ab)

let compare_ints a b cmpb =
  cmpb land cmpint a b (a land b)

let bmask p =
  (lnot p) lxor (p - 1)

let bmask2 p = 
  -branchbit p lsl 1

let compare_fast a b cmpb = 
  let pa = get_prefix a in
  let pb = get_prefix b in
  let ma = bmask pa in
  let mb = bmask pb in
  let m = ma land mb in
  if (pa land m) == (pb land m) then
    cmpb land cmpint mb ma m
  else
    cmp_incomparable

let rec compare_nonempty a b cmpb =
  if cmpb == 0 then 0 else
  let pa = get_prefix a in
  let pb = get_prefix b in
  if pa == pb then
    (* trees have same prefix, compare subtrees *)
    match a, b with
    | Branch (pfxa, a0, a1), Branch (pfxb, b0, b1) ->
      compare_nonempty a0 b0 (compare_nonempty a1 b1 (compare_fast a0 b0 cmpb))
    | Leaf (pa, xa), Leaf (pb, xb) ->
      cmp_incomparable (* FIXME *)
    | _ -> assert false
  else
    let bra = branchbit pa in
    let ma = -bra in
    let brb = branchbit pb in
    let mb = -brb in
    let mshort = ma land mb in
    if eqmask (mshort lsl 1) pa pb then
      (* one prefix is contained in the other *)
      if mshort == ma then
        match a with
        | Branch (pfxa, a0, a1) ->
          (* A has a shorter prefix *)
          let cmpb = cmpb land cmp_a_not_sub in
          if pb land bra == 0 then
            compare_nonempty a0 b cmpb
          else
            compare_nonempty a1 b cmpb
        | _ -> assert false
      else
        match b with 
        | Branch (pfxb, b0, b1) ->
          (* B has a shorter prefix *)
          let cmpb = cmpb land cmp_b_not_sub in
          if pa land brb == 0 then
            compare_nonempty a b0 cmpb
          else
            compare_nonempty a b1 cmpb
        | _ -> assert false
    else
      (* the two prefixes are incompatible *)
      cmp_incomparable

(*
let compare a b = 
  match a, b with
  | Empty _, Empty _ -> Equal
  | Empty _, b -> Subset
  | a, Empty _ -> Superset
  | a, b -> comparison_of_cmp_info (compare_nonempty a b cmp_no_info)

let subset a b =
  match a, b with
  | Empty _, _ -> true
  | _, Empty _ -> false
  | a, b -> 
    let cmpb = compare_nonempty a b cmp_no_info in
    cmpb land (lnot cmp_a_not_sub) != 0


*)
*)
*)
