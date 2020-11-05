(* Later, maybe intern these? *)

(* FIXME: preserve ordering of tuple fields in mixtures,
   to avoid screwing up evaluation order.
   (Alt: ban mixtures in the parser) *)

type symbol = string
module SymMap = Map.Make (struct type t = string let compare = compare end)

type field_name = Field_positional of int | Field_named of symbol
module FieldMap = Map.Make (struct type t = field_name let compare = compare end)

let string_of_field_name = function
  | Field_named s -> s
  | Field_positional i -> Printf.sprintf ".%d" i

type +'a tuple_fields =
  { fields : 'a FieldMap.t;
    fnames : field_name list;
    fopen : [`Open|`Closed] }

type 'a field_syntax =
  | Fpos of 'a
  | Fnamed of symbol * 'a
  | Fdots
  | Fempty

let rec collect_fields npos fields fnames_rev = function
  | ([] | [Fempty] | [Fdots]) as tail ->
     let fopen = match tail with [Fdots] -> `Open | _ -> `Closed in
     { fields; fnames = List.rev fnames_rev; fopen }
  | field :: rest ->
     let name, value, npos =
       match field with
       | Fpos v -> Field_positional npos, v, npos+1
       | Fnamed (s, v) -> Field_named s, v, npos
       | Fdots -> failwith "'...' can only appear at the end"
       | Fempty -> assert false in
     let fields =
       if FieldMap.mem name fields then
         failwith ("duplicate field names " ^ string_of_field_name name);
       FieldMap.add name value fields in
     collect_fields npos fields (name :: fnames_rev) rest

let collect_fields fs = collect_fields 0 FieldMap.empty [] fs

let map_fields f fs =
  { fs with fields = FieldMap.mapi (fun fn x -> f fn x) fs.fields }

let fold_fields f (acc : 'acc) fs =
  List.fold_left (fun acc n ->
      f acc n (FieldMap.find n fs.fields)) acc fs.fnames

let fold2_fields ~left ~both ~right (acc : 'acc) fs1 fs2 =
  let rec named remaining2 acc names1 =
    match names1 with
    | [] ->
       List.fold_left (fun acc n2 ->
         if FieldMap.mem n2 remaining2 then
           right acc n2 (FieldMap.find n2 remaining2)
         else
           acc) acc fs2.fnames
    | n1 :: names1 ->
       if FieldMap.mem n1 remaining2 then
         let acc = both acc n1
                     (FieldMap.find n1 fs1.fields)
                     (FieldMap.find n1 remaining2) in
         named (FieldMap.remove n1 remaining2) acc names1
       else
         let acc = left acc n1
                     (FieldMap.find n1 fs1.fields) in
         named remaining2 acc names1 in
  named fs2.fields acc fs1.fnames
