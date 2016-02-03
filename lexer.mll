{
open Lexing

module Make (L : Location.Locator) = struct
module P = Parser.Make (L)
open P


type state =
  | Toplevel
  | Block
  | Paren
  | Bracket
  | Brace

type action =
  | Nop
  | Push of state
  | Pop of state


let terminator = function
| Toplevel -> EOF
| Block -> END
| Paren -> RPAR
| Bracket -> RBRACK
| Brace -> RBRACE

let tok t = (t, Nop, [])
let bopen t s = (t, Push s, [])
let bclose t s = (t, Pop s, [])
let err e (t, s, es) = (t, Nop, e :: es)

let significant_newline = function
| Block | Toplevel -> true
| Paren | Bracket | Brace -> false

}

let int = ['1'-'9'] ['0'-'9']* | '0'
let digit = ['0'-'9']
let float = digit* '.' digit*? ['e' 'E'] ['-' '+']? digit+?
let nl = '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

let nl_or_comments = ( '\n' | "\r\n" | "//" [^ '\n' '\r']* )+

rule lex s =
  parse
  | [' ' '\t']+ { lex s lexbuf }
  | nl_or_comments { if significant_newline s then tok NL else lex s lexbuf }
  | "("      { bopen LPAR Paren }
  | ")"      { bclose RPAR Paren }
  | "{"      { bopen LBRACE Brace }
  | "}"      { bclose RBRACE Brace }
  | "["      { bopen LBRACK Bracket }
  | "]"      { bclose RBRACK Bracket }

  | "->"     { tok ARROW }
  | ","      { tok COMMA }
  | ";"      { tok SEMI }
  | "."      { tok DOT }
  | "|"      { tok OR }
  | "&"      { tok AND }
  | ":"      { tok COLON }
  | "<:"     { tok SUBSUME }
  | "rec"    { tok REC }
  | "="      { tok EQUALS }
  | "fun"    { tok FUN }
  | "unit"   { tok UNIT }
  | "let"    { tok LET }
  | "in"     { tok IN }
  | "true"   { tok TRUE }
  | "false"  { tok FALSE }
  | "if"     { tok IF }
  | "then"   { tok THEN }
  | "else"   { tok ELSE }
  | "def"    { bopen DEF Block }
  | "end"    { bclose END Block }
  | "type"   { tok TYPE }
  | "any"    { tok ANY }
  | "nothing"{ tok NOTHING }

  | "=="     { tok EQEQUALS }
  | "<"      { tok CMP_LT }
  | ">"      { tok CMP_GT }
  | "<="     { tok CMP_LTE }
  | ">="     { tok CMP_GTE }
  | "+"      { tok PLUS }
  | "-"      { tok MINUS }
  | "_"      { tok UNDER }

  | "list"   { tok LIST }
  | "::"     { tok CONS }
  | "match"  { tok MATCH }
  | "with"   { tok WITH }

  | id       { tok (IDENT (Symbol.intern (Lexing.lexeme lexbuf))) }
  | int      { tok (INT (int_of_string (Lexing.lexeme lexbuf))) }
  | eof      { bclose EOF Toplevel}

{
end
}
