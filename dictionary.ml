(* multiplier (always odd) and shift count *)
type hash_params = int * int


let rec prob_collision_free n buckets acc =
  if n = 0 then acc else
  prob_collision_free (n-1) buckets
    (acc *. float_of_int (buckets - (n - 1)) /. float_of_int buckets)

let rec pow2 n = 1 lsl n

let rec estimate_size n eps k =
  if prob_collision_free n (pow2 k) 1. > eps then k else estimate_size n eps (k + 1)
let estimate_size n eps = estimate_size n eps 0



let shift hbits =
  let intbits = Sys.word_size - 1 in
  intbits - hbits

let check_for_duplicates keys =
  let h = Hashtbl.create 20 in
  Array.iter (fun k ->
    if Hashtbl.mem h k then failwith "Table has duplicate keys";
    Hashtbl.add h k ()) keys

let pos sym m s =
  (Symbol.hash sym * m) lsr s

let try_hashtable_size (keys : Symbol.t array) (bits : int) =
  let buckets = Array.make (pow2 bits) false in
  let s = shift bits in
  let m = Int64.to_int (Random.int64 Int64.max_int) lor 1 in
  let rec ok s m buckets keys n len =
    if n = len then true else
    let p = pos keys.(n) m s in
    if buckets.(p) then false else
    (buckets.(p) <- true; ok s m buckets keys (n + 1) len) in
  match (ok s m buckets keys 0 (Array.length keys)) with
    false -> None
  | true -> Some (m, s, pow2 bits)


let find_hashtable (keys : int array) =
  check_for_duplicates keys;
  let rec search b tries =
    if tries = 5000 then search (b + 1) 0
    else match try_hashtable_size keys b with
    | None -> search b (tries + 1)
    | Some ans -> ans in
  search (estimate_size (Array.length keys) 0.001) 0


type 'a t = hash_params * 'a option array

let generate (table : (Symbol.t * 'a) list) : 'a t =
  let (m, s, nbuckets) =
    find_hashtable (Array.of_list (List.map (fun (sym, x) -> sym) table)) in
  assert (m land 1 = 1);
  let a = Array.make nbuckets None in
  List.iter (fun (sym, x) -> a.(pos sym m s) <- Some x) table;
  ((m, s), a)
