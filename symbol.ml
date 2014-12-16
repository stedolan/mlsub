let sym_table = Hashtbl.create 20
let id_table = Hashtbl.create 20
  
type t = int

let next_id = ref 0
let fresh () = let x = !next_id in (incr next_id; x)

let intern (s : string) : t = 
  try Hashtbl.find sym_table s
  with Not_found -> 
    let n = fresh () in
    Hashtbl.add sym_table s n;
    Hashtbl.add id_table n s;
    n
      
let to_string (n : t) : string = Hashtbl.find id_table n
