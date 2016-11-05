module type Locator = sig
  val pos : int * int -> Location.t
end

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
| Token of P.token * int * int * L.action

type lstack =
| Empty
| Nest of L.state * P.token * Location.t * lstack

let buf = Sedlexing.Utf8.from_string Src.src.contents

let get_state = function
| Empty -> L.Toplevel
| Nest (state, _, _, _) -> state

let read_token state =
  match L.lex (get_state state) buf with
  | (token, action, errs') ->
     Token (token, Sedlexing.lexeme_start buf, Sedlexing.lexeme_end buf, action)
  | exception L.Bad_token ->
     raise (Error.Fatal (Error.Syntax (Location.Loc (Src.src, Sedlexing.lexeme_start buf, Sedlexing.lexeme_end buf))))

let tokloc (Token (_, s, e, _)) = Location.Loc (Src.src, s, e)

let pos s e = Location.Loc (Src.src, s, e)

let accept_token lstack (Token (tok, startpos, endpos, action) as fulltok) =
  match action, lstack with
  | L.Nop, lstack -> lstack
  | L.Push s, lstack -> Nest (s, tok, pos startpos endpos, lstack)
  | L.Pop s', Nest (s, _, _, lstack) when s = s' -> lstack
  | L.Pop s', Empty ->
     Error.(fatal (Unmatched_closing_delim (tokloc fulltok)))
  | L.Pop s', Nest (_, _, loc, _) ->
     Error.(fatal (Mismatched_closing_delim (loc, tokloc fulltok)))


let rec skip_bad_tokens startpos lstack = function
  | Token (P.EOF, _, endpos, _) -> Error.(fatal (Syntax (Location.Loc (Src.src, startpos, endpos))))
  | tok -> match accept_token lstack tok with
    | Empty ->
       let endpos = match tok with Token (_, _, endpos, _) -> endpos in
       Error.(Syntax (pos startpos endpos))
    | lstack -> skip_bad_tokens startpos lstack (read_token lstack)

let skip_bad_tokens tok =
  skip_bad_tokens (match tok with Token (_, s, _, _) -> s) Empty tok

let finish_lexer v = function
| Empty -> v
| _ -> Error.internal "lexer stack nonempty after parser completed"


let to_lexpos n = Lexing.{ pos_fname = ""; pos_cnum = n; pos_lnum = 0; pos_bol = 0  }

let rec run_parser err lstack tok = function
  | I.Accepted v -> finish_lexer v lstack
  | I.Rejected -> Error.(raise (Fatal (Syntax (tokloc tok)))) 
  | I.InputNeeded _ as chk ->
     let lstack = accept_token lstack tok in
     let (Token (t, startpos, endpos, _) as tok) = read_token lstack in
     run_parser err lstack tok (I.offer chk (t, to_lexpos startpos, to_lexpos endpos))
  | (I.Shifting _ | I.AboutToReduce _) as chk ->
     run_parser err lstack tok (I.resume chk)
  | I.HandlingError _ as chk ->
     err (skip_bad_tokens tok);

     let rec handle henv = match I.resume henv with
       | (I.HandlingError _ | I.Shifting _ | I.AboutToReduce _) as chk -> handle chk
       | I.InputNeeded _ as chk ->
          let (Token (t, startpos, endpos, _) as tok) = read_token lstack in
          run_parser err lstack tok (I.offer chk (t, to_lexpos startpos, to_lexpos endpos))
       | I.Accepted v -> finish_lexer v lstack
       | I.Rejected -> Error.(raise (Fatal (Syntax (tokloc tok)))) in
     handle chk

let parse err =
  let lstate = Empty in
  let (Token (t, s, e, _) as tok) = read_token lstate in
  let p = match P.Incremental.modlist (to_lexpos s) with 
    | I.InputNeeded _ as chk -> I.offer chk (t, to_lexpos s, to_lexpos e)
    | _ -> Error.internal "parser initialisation error" in
  run_parser err Empty tok p 
end

let parse_modlist err src =
  let module R = ReadSource (struct let src = src end) in
  R.parse err
