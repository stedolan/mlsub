{
open Lexing
open Parser

exception SyntaxError of string
}


let int = ['1'-'9'] ['0'-'9']*


let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?


let white = [' ' '\t' '\n' '\r']+
let comment = '(' '*' ( [^ '*']* | '*' [^ ')']) * '*' ')'
let id = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*


rule read =
  parse
  | white    { read lexbuf }
  | comment  { read lexbuf }
  | "->"     { ARROW }
  | "("      { LPAR }
  | ")"      { RPAR }
  | "{"      { LBRACE }
  | "}"      { RBRACE }
  | ","      { COMMA }
  | "."      { DOT }
  | "|"      { TY_JOIN }
  | "&"      { TY_MEET }
  | ":"      { ASC }
  | "<:"     { SUBSUME }
  | "Top"    { TOP }
  | "Bot"    { BOT }
  | "rec"    { REC }
  | "="      { EQUALS }
  | "fun"    { FUN }
  | "unit"   { UNIT }
  | "let"    { LET }
  | "in"     { IN }
  | "true"   { TRUE }
  | "false"  { FALSE }
  | "if"     { IF }
  | "then"   { THEN }
  | "else"   { ELSE }

  | "list"   { LIST }
  | "[]"     { NIL }
  | "::"     { CONS }
  | "match"  { MATCH }
  | "with"   { WITH }

  | id       { IDENT (Lexing.lexeme lexbuf) }
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof      { EOF }
