let sym_table = Hashtbl.create 20
let id_table = Hashtbl.create 20
  
type t = int

let next_id = ref 0
let fresh_id () = let x = !next_id in (incr next_id; x)

let intern (s : string) : t = 
  try Hashtbl.find sym_table s
  with Not_found -> 
    let n = fresh_id () in
    Hashtbl.add sym_table s n;
    Hashtbl.add id_table n s;
    n
      
let to_string (n : t) : string = Hashtbl.find id_table n


                                              
let fresh_name_ctr = ref 0
let rec fresh s =
  incr fresh_name_ctr;
  let v = s ^ "_" ^ string_of_int !fresh_name_ctr in
  if Hashtbl.mem sym_table v then fresh v else intern v
