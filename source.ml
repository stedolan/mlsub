module type Locator = sig
  val pos : Lexing.position * Lexing.position -> Location.t
end

open Lexing
open Location

module ReadSource (Src : sig val src : Location.source end) = struct

module Loc : Location.Locator = struct
  let pos (p, p') = Location.Loc (Src.src, 
     p.Lexing.pos_cnum, p'.Lexing.pos_cnum)
end

module L = Lexer.Make(Loc)
module P = Parser.Make(Loc)
module I = P.MenhirInterpreter

type token =
| Token of P.token * Lexing.position * Lexing.position * L.action

type lstack =
| Empty
| Nest of L.state * P.token * Location.t * lstack

let buf = Lexing.from_string Src.src.contents

let get_state = function
| Empty -> L.Toplevel
| Nest (state, _, _, _) -> state

let read_token state =
  match L.lex (get_state state) buf with
  | (token, action, errs') ->
     Token (token, buf.lex_start_p, buf.lex_curr_p, action)
  | exception L.Bad_token ->
     raise (Error.Fatal (Error.Syntax (Loc.pos (buf.lex_start_p, buf.lex_curr_p))))

let tokloc (Token (_, s, e, _)) = Loc.pos (s, e)

let accept_token lstack (Token (tok, startpos, endpos, action) as fulltok) =
  match action, lstack with
  | L.Nop, lstack -> lstack
  | L.Push s, lstack -> Nest (s, tok, Loc.pos (startpos, endpos), lstack)
  | L.Pop s', Nest (s, _, _, lstack) when s = s' -> lstack
  | L.Pop s', Empty ->
     Error.(fatal (Unmatched_closing_delim (tokloc fulltok)))
  | L.Pop s', Nest (_, _, loc, _) ->
     Error.(fatal (Mismatched_closing_delim (loc, tokloc fulltok)))


let rec skip_bad_tokens startpos lstack = function
  | Token (P.EOF, _, endpos, _) -> Error.(fatal (Syntax (Loc.pos (startpos, endpos))))
  | tok -> match accept_token lstack tok with
    | Empty ->
       let endpos = match tok with Token (_, _, endpos, _) -> endpos in
       Error.(Syntax (Loc.pos (startpos, endpos)))
    | lstack -> skip_bad_tokens startpos lstack (read_token lstack)

let skip_bad_tokens tok =
  skip_bad_tokens (match tok with Token (_, s, _, _) -> s) Empty tok

let finish_lexer v = function
| Empty -> v
| _ -> Error.internal "lexer stack nonempty after parser completed"



let rec run_parser err lstack tok = function
  | I.Accepted v -> finish_lexer v lstack
  | I.Rejected -> Error.(raise (Fatal (Syntax (tokloc tok)))) 
  | I.InputNeeded env ->
     let lstack = accept_token lstack tok in
     let (Token (t, startpos, endpos, _) as tok) = read_token lstack in
     run_parser err lstack tok (I.offer env (t, startpos, endpos))
  | I.HandlingError env ->
     err (skip_bad_tokens tok);

     let rec handle henv = match I.handle henv with
       | I.HandlingError henv' -> handle henv'
       | I.InputNeeded env ->
          let (Token (t, startpos, endpos, _) as tok) = read_token lstack in
          run_parser err lstack tok (I.offer env (t, startpos, endpos))
       | I.Accepted v -> finish_lexer v lstack
       | I.Rejected -> Error.(raise (Fatal (Syntax (tokloc tok)))) in
     handle env

let parse err =
  let lstate = Empty in
  let (Token (t, s, e, _) as tok) = read_token lstate in
  let p = match P.modlist_incremental () with 
    | I.InputNeeded env -> I.offer env (t, s, e)
    | _ -> Error.internal "parser initialisation error" in
  run_parser err Empty tok p 
end


let parse_modlist err src =
  let module R = ReadSource (struct let src = src end) in
  R.parse err
