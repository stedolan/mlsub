(* Later, maybe intern these? *)
type symbol = string
module SymMap = Map.Make (struct type t = string let compare = compare end)

type field_name = Field_positional of int | Field_named of symbol
module FieldMap = Map.Make (struct type t = field_name let compare = compare end)

let equal_field_name = (=)

let string_of_field_name = function
  | Field_named s -> s
  | Field_positional i -> Printf.sprintf ".%d" i
