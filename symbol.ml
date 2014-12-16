let sym_table = Hashtbl.create 20
let id_table = Hashtbl.create 20
  
type t = int


(* Slightly dodgy FNV-1a hash (63-bit precision instead of 64) *)
let fnv_prime = 1099511628211
let fnv_offset_basis = -3750763034362895579 (* masked FNV-1a offset basis *)
let fnv_hash str =
  let rec hash_bytes str n len h =
    if n = len then h else
    hash_bytes str (n + 1) len ((h lxor (Char.code str.[n])) * fnv_prime) in
  hash_bytes str 0 (String.length str) fnv_offset_basis


let next_id = ref 0
let fresh_id () = let x = !next_id in (incr next_id; x)

let intern (s : string) : t = 
  try Hashtbl.find sym_table s
  with Not_found -> 
    let n = fresh_id () in
    Hashtbl.add sym_table s n;
    Hashtbl.add id_table n (s, fnv_hash s);
    n
      
let to_string (n : t) : string = let (s, h) = Hashtbl.find id_table n in s
let hash (n : t) : int = let (s, h) = Hashtbl.find id_table n in h


                                              
let fresh_name_ctr = ref 0
let rec fresh s =
  incr fresh_name_ctr;
  let v = s ^ "_" ^ string_of_int !fresh_name_ctr in
  if Hashtbl.mem sym_table v then fresh v else intern v
