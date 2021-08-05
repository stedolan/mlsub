type t =
  { loc_start : Lexing.position;
    loc_end : Lexing.position }

let subset s t =
  let precedes (s : Lexing.position) (t : Lexing.position) =
    s.pos_fname = t.pos_fname && s.pos_cnum <= t.pos_cnum in
  precedes t.loc_start s.loc_start && precedes s.loc_end t.loc_end

type location = t

let noloc =
  let loc : Lexing.position = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0} in
  { loc_start = loc; loc_end = loc}

let mark =
  let loc : Lexing.position = {pos_fname="MARK";pos_lnum=1;pos_cnum=0;pos_bol=0} in
  { loc_start = loc; loc_end = loc}

type set = location list

let single l = [l]

let union = (@)

let empty = []
