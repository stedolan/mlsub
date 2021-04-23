type t =
  { source : string;
    loc_start : Lexing.position;
    loc_end : Lexing.position }

type location = t

let noloc =
  let loc : Lexing.position = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0} in
  { source = "_"; loc_start = loc; loc_end = loc}

type set = location list

let single l = [l]

let union = (@)

let empty = []
