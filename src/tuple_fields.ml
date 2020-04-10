(* Later, maybe intern these? *)

type symbol = string
module SymMap = Map.Make (struct type t = string let compare = compare end)

type 'a tuple_fields =
  { fpos : 'a list;
    fnamed : 'a SymMap.t;
    fnames : symbol list;
    fopen : [`Open|`Closed] }

type 'a field_syntax =
  | Fpos of 'a
  | Fnamed of symbol * 'a
  | Fdots
  | Fempty

let rec collect_fields pos named = function
  | ([] | [Fempty] | [Fdots]) as tail ->
     let fpos = List.rev pos in
     let fnamed = List.rev named in
     let fnames = List.map fst fnamed in
     let fnamed =
       List.fold_left (fun acc (s, x) ->
         if SymMap.mem s acc then
           failwith ("duplicate field names " ^ s);
         SymMap.add s x acc) SymMap.empty fnamed in
     let fopen = match tail with [Fdots] -> `Open | _ -> `Closed in
     { fpos; fnamed; fnames; fopen }
  | Fempty :: _ -> assert false
  | Fdots :: _ ->
     failwith "'... can only appear at the end of a tuple"
  | Fpos p :: fs ->
     collect_fields (p :: pos) named fs
  | Fnamed (s, x) :: fs ->
     collect_fields pos ((s, x) :: named) fs

let collect_fields fs = collect_fields [] [] fs

let map_fields f fs =
  { fs with
    fpos = List.map f fs.fpos;
    fnamed = SymMap.map f fs.fnamed }
let fold_fields f (acc : 'acc) fs =
  let acc = List.fold_left (fun acc x -> f acc x) acc fs.fpos in
  let acc = List.fold_left (fun acc n ->
                f acc (SymMap.find n fs.fnamed)) acc fs.fnames in
  acc

type field_name = Field_positional of int | Field_named of symbol

let fold2_fields ~left ~both ~right (acc : 'acc) fs1 fs2 =
  let rec pos i acc ps1 ps2 =
    match ps1, ps2 with
    | [], [] -> acc
    | [], p2 :: ps2 ->
       let acc = right acc (Field_positional i) p2 in
       pos (i+1) acc [] ps2
    | p1 :: ps1, [] ->
       let acc = left acc (Field_positional i) p1 in
       pos (i+1) acc ps1 []
    | p1 :: ps1, p2 :: ps2 ->
       let acc = both acc (Field_positional i) p1 p2 in
       pos (i+1) acc ps1 ps2 in
  let acc = pos 0 acc fs1.fpos fs2.fpos in
  let rec named remaining2 acc names1 =
    match names1 with
    | [] ->
       List.fold_left (fun acc n2 ->
         if SymMap.mem n2 remaining2 then
           right acc (Field_named n2) (SymMap.find n2 remaining2)
         else
           acc) acc fs2.fnames
    | n1 :: names1 ->
       if SymMap.mem n1 remaining2 then
         let acc = both acc
                     (Field_named n1)
                     (SymMap.find n1 fs1.fnamed)
                     (SymMap.find n1 remaining2) in
         named (SymMap.remove n1 remaining2) acc names1
       else
         let acc = left acc
                     (Field_named n1)
                     (SymMap.find n1 fs1.fnamed) in
         named remaining2 acc names1 in
  let acc = named fs2.fnamed acc fs1.fnames in
  acc

(*

let fold_fields f acc fs =
  let acc = List.fold_left (fun acc (d, _) -> f acc d) acc fs.fields_pos in
  let acc = List.fold_left (fun acc (_, d, _) -> match d with None -> acc | Some d -> f acc d) acc fs.fields_named in
  acc
 *)
