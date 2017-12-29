module M = Intmap.Make (struct type t = int let get_id n = n end)
open M


let verify (x : M.t) = Intmap.verify (Obj.magic x)

(* an evil random number generator, biased towards edge cases *)
let randint () =
  match Random.int 50 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 as n -> 1 lsl (n * 4)
  | 9 -> 1 lsl 63
  | 10 -> 0
  | 11 -> -1
  | 12 -> 1
  | 13 -> max_int
  | 14 -> min_int
  | n when n < 30 -> 
    -2000 + Random.int 4000
  | n ->
      Random.bits () - Random.bits ()

let rec randlist = function
  | 0 -> []
  | n -> randint () :: randlist (n - 1)

let rec compress = function
  | a :: (b :: _ as t) ->
    if a = b then compress t else a :: compress t
  | smaller -> smaller

let set_of_array xs =
  (* construct a set by repeated insertion *)
  let rec find_p2 k n = if k * 2 <= n then find_p2 (k * 2) n else k in
  let p2 = find_p2 1 (Array.length xs) in
  Printf.printf "%d %d\n" (Array.length xs) p2;
  let permute n =
    let n = (n + 432875) mod (Array.length xs) in
    assert (n < Array.length xs);
    let low = n land (p2 - 1) in
    let high = n land (lnot (p2 - 1)) in
    if high = 0 then
      (low * 4352617) land (p2 - 1)
    else n in
  let s = ref empty in
  for i = 0 to Array.length xs - 1 do
    s := add !s xs.(permute i)
  done;
  verify !s;
  !s

let mk_set xs = 
  let elts = compress (List.sort compare xs) in
  let s = of_list xs in
  verify s;
  assert (length s = List.length elts);
  assert (s = List.fold_left union empty (List.map singleton xs));
  assert (s = List.fold_right union (List.map singleton xs) empty);
  assert (s = set_of_array (Array.of_list xs));

  let elts' = to_list s in
  assert (elts' = List.sort compare elts');
  assert (elts' = elts);

  let a = Array.of_list elts in
  let i = ref 0 in
  iter s (fun n -> assert (n = a.(!i)); incr i);
  let i = ref 0 in
  let _ = fold_left s 0 (fun k n -> assert (k = !i); assert (n = a.(!i)); incr i; k+1) in

  s

let randset n = mk_set (randlist n)


let rec randsets k = function
  | 0 -> []
  | n -> randset (Random.int k) :: randsets k (n - 1)

let semilattice f x y z =
  let f a b = 
    let r = f a b in
    verify r;
    assert (r = mk_set (to_list r));
    r in
  (f x y = f y x) && (* commutative *)
  (f x (f y z) = f (f x y) z) && (* associative *)
  (f x x = x) (* idempotent *)


let test n =
  let x = randset (Random.int n) 
  and y = randset (Random.int n)
  and z = randset (Random.int n) in
  assert (semilattice union x y z);
  assert (semilattice inter x y z);
  assert (union x (inter y z) = inter (union x y) (union x z));
  assert (inter x (union y z) = union (inter x y) (inter x z));
  assert (subset (union x y) z = subset x (diff z y));
  assert (subset (inter x y) x);
  assert (subset x (union x y));
  let xy = inter x y in
  List.iter (fun n -> assert (mem xy n = mem x n && mem y n)) (randlist n);
  let xy = union x y in
  List.iter (fun n -> assert (mem xy n = mem x n || mem y n)) (randlist n);
  if subset y z then iter y (fun n -> assert (mem z n))
  else assert (fold_left y false (fun b n -> b || mem z n));
  (x, y, z)


let _ = test 100

(*
let subseteq a b = 
  let s = match Intmap.compare a b with
    | Subset | Equal -> true
    | _ -> false in
  assert (s == Intmap.subset a b);
  s




let edge_numbers = [0;1;63;64;127;-32;-1;min_int;max_int;128 * 43244;40]

let edge_set n = List.fold_left (fun s (i,x) -> 
  if n land (1 lsl i) == 0 then s else union s (singleton x)) empty (List.mapi (fun i x -> (i,x)) edge_numbers)

let rec edge_sets acc = function
  | 0 -> acc
  | n -> edge_sets (edge_set (n-1) :: acc) (n - 1)

let dump_set s = List.iter (fun n -> print_int n; print_string "\n") (to_list s)

let test_cmp () =
  let sets = edge_sets [] (1 lsl List.length edge_numbers) in
  List.iteri (fun i a ->
    List.iteri (fun j b ->
      match Intmap.compare a b with
      | Subset -> assert (i lor j == j)
      | Superset -> assert (i lor j == i)
      | Equal -> assert (i = j)
      | Incomparable -> assert (i land j != i && i land j != j)
    ) sets) sets

let benchmark_cmp () = 
  let sets = randsets 500 1000 in
  List.iter (fun a -> List.iter (fun b -> let _ = Intmap.compare a b in ()) sets) sets


let test_member s = 
  List.iter (fun x -> assert (Intmap.mem s x)) (to_list s);
  let h = Hashtbl.create 100 in
  List.iter (fun x -> Hashtbl.add h x ()) (to_list s);
  List.iter (fun x -> assert (Intmap.mem s x == Hashtbl.mem h x)) (randlist 1000)


(* let _ = benchmark_cmp () *)



let _ = 
  for i = 1 to 10 do test_member (randset (Random.int 10000)) done;
  test_member empty
let _ = test_cmp () 
let retest () =
  for i = 1 to 10 do let _ = test 100 in () done
let _ = retest ()

*)
