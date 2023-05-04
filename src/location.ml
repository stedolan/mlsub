type span =
  { loc_start : Lexing.position;
    loc_end : Lexing.position }

(* Locations can be discontiguous and in general consist of several spans *)
type t = span list

type location = t

type 'a loc = 'a * location

let subspan s t =
  let precedes (s : Lexing.position) (t : Lexing.position) =
    s.pos_fname = t.pos_fname && s.pos_cnum <= t.pos_cnum in
  precedes t.loc_start s.loc_start && precedes s.loc_end t.loc_end

let subset s t =
  s |> List.for_all (fun s ->
    t |> List.exists (fun t ->
      subspan s t))

let equal s t =
  subset s t && subset t s

let noloc : t =
  let loc : Lexing.position = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0} in
  [{ loc_start = loc; loc_end = loc}]

let mark : t=
  let loc : Lexing.position = {pos_fname="MARK";pos_lnum=1;pos_cnum=0;pos_bol=0} in
  [{ loc_start = loc; loc_end = loc}]
