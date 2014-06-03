open Lexer
open Lexing

open Printf

let parse_with_error lexbuf =
  try Some (Parser.exp Lexer.read lexbuf) with
  | SyntaxError _ | Parser.Error ->
    fprintf stderr "nope\n%!"; None

(* part 1 *)
let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    printf "%s\n%!" value;
    parse_and_print lexbuf
  | None -> parse_and_print lexbuf

let lexbuf = Lexing.from_channel stdin;;
parse_and_print lexbuf
(*
let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx

(* part 2 *)
let () =
  Command.basic ~summary:"Parse and display JSON"
    Command.Spec.(empty +> anon ("filename" %: file))
    loop 
  |> Command.run
*)
