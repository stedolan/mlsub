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
  let rec run ls ps errs = match ls, ps with
    | [], I.Accepted v -> v
    | (loc, s) :: lsrest, I.InputNeeded env -> begin

      let (token, action, errs') = L.lex s buf in
(*
      Location.print Format.std_formatter (Loc.pos (buf.lex_start_p, buf.lex_curr_p));
      Format.printf "%!";
*)
      let errs = errs @ errs' in
      let ps = I.offer env (token, buf.lex_start_p, buf.lex_curr_p) in
      match action with
      | L.Nop -> 
         run ls ps errs
      | L.Push s' -> 
         run ((Loc.pos (buf.lex_start_p, buf.lex_curr_p), s') :: ls) ps errs
      | L.Pop s' when s = s' ->
         run lsrest ps errs
      | L.Pop s' ->
         failwith "bad nesting"
    end
    | ls, I.HandlingError env -> (Printf.printf "handling\n%!"; run ls (I.handle env) errs)
    | _, I.Rejected -> failwith "rejected" 
    | _ :: _, I.Accepted v -> failwith "surplus junk" 
    | [], I.InputNeeded env -> failwith "unexpected eof" in



  run [(Location.internal, L.Toplevel)] (P.modlist_incremental ()) []
  
