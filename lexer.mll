{
open Lexing
open Parser

exception SyntaxError of string
}

(* part 1 *)
let int = '-'? ['0'-'9'] ['0'-'9']*

(* part 2 *)
let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?

(* part 3 *)
let white = [' ' '\t' '\n' '\r']+
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

(* part 4 *)
rule read =
  parse
  | white    { read lexbuf }
  | id       { IDENT (Lexing.lexeme lexbuf) }
  | "->"     { ARROW }
  | "fun"    { FUN }
