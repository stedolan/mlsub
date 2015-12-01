open Lexing

type t =
  | Pos of Lexing.position * Lexing.position

let contains (Pos (p, p')) (Pos (q, q')) =
  p.pos_fname = q.pos_fname && p.pos_bol <= q.pos_bol && p'.pos_bol >= q'.pos_bol

