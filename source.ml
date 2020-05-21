module type Locator = sig
  val pos : Lexing.position * Lexing.position -> Location.t
end

open Lexing
open Location

let parse_modlist src =
  let module Loc : Location.Locator = struct
    let pos (p, p') = Location.Loc (src, 
        p.Lexing.pos_cnum, p'.Lexing.pos_cnum)
  end in
  let module L = Lexer.Make (Loc) in
  let module P = Parser.Make (Loc) in
  let module I = P.MenhirInterpreter in
  let buf = Lexing.from_string src.contents in
  P.modlist L.read buf
  
