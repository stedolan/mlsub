module Make (L : Location.Locator) = struct

module P = Parser.Make(L)
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

exception Bad_token


let ucase = [%sedlex.regexp? 'A'..'Z']
let lcase = [%sedlex.regexp? 'a'..'z']

let id = [%sedlex.regexp? ('a'..'z'|'A'..'Z'|'_'), Star('a'..'z'|'A'..'Z'|'0'..'9'|'_')]
let int = [%sedlex.regexp? (('1'..'9'),Star('0'..'9')) | '0']

let string = [%sedlex.regexp? '"',Star(Compl('"')),'"'] (* FIXME: escaping *)

let nl_or_comments = 
  [%sedlex.regexp? Plus( '\n' | "\r\n" | "//",  Star(Compl('\n'|'\r')))]

let significant_newline = function
| Brace | Block | Toplevel -> true
| Paren | Bracket -> false

let tok t = (t, Nop, [])
let bopen t s = (t, Push s, [])
let bclose t s = (t, Pop s, [])

let lexeme buf =
  Sedlexing.Utf8.lexeme buf

let rec lex s buf =
  match%sedlex buf with
  | Plus(' ' | '\t') -> lex s buf
  | nl_or_comments -> if significant_newline s then tok NL else lex s buf
  | "(" -> bopen LPAR Paren
  | ")" -> bclose RPAR Paren
  | "{" -> bopen LBRACE Brace
  | "}" -> bclose RBRACE Brace
  | "[" -> bopen LBRACK Bracket
  | "]" -> bclose RBRACK Bracket

  | "->"     -> tok ARROW
  | "=>"     -> tok DARROW
  | ","      -> tok COMMA
  | "'"      -> tok SQUOT
  | ";"      -> tok SEMI
  | "."      -> tok DOT
  | "|"      -> tok OR
  | "&"      -> tok AND
  | ":"      -> tok COLON
  | "<:"     -> tok SUBSUME
  | "rec"    -> tok REC
  | "="      -> tok EQUALS
  | "let"    -> tok LET
  | "true"   -> tok TRUE
  | "false"  -> tok FALSE
  | "if"     -> tok IF
(*  | "then"   -> tok THEN*)
  | "else"   -> tok ELSE
  | "def"    -> tok DEF
(*  | "do"     -> bopen DO Block
  | "end"    -> bclose END Block*)
  | "type"   -> tok TYPE
  | "any"    -> tok ANY
  | "nothing"-> tok NOTHING

  | "=="     -> tok EQEQUALS
  | "<"      -> tok LT
  | ">"      -> tok GT
  | "<="     -> tok LTE
  | ">="     -> tok GTE
  | "+"      -> tok PLUS
  | "-"      -> tok MINUS
  | "_"      -> tok UNDER

  | "::"     -> tok CONS
  | "match"  -> tok MATCH
  | "case"   -> tok CASE

  | id       -> tok (IDENT (Symbol.intern (lexeme buf)))
  | int      -> tok (INT (int_of_string (lexeme buf)))
  | string   -> tok (STRING (let s = lexeme buf in String.(sub s 1 (length s - 2))))
  | eof      -> tok EOF

  | _ -> raise Bad_token

end
