open Grammar
open Sedlexing
open Sedlexing.Utf8
let lex buf =
  match%sedlex buf with
  | Plus(' ' | '\t') -> WS
  | '\n' | "\r\n" -> NL
  | "//", Star(Compl('\n'|'\r')) -> COMMENT

  | '(' -> LPAR
  | ')' -> RPAR
  | '[' -> LBRACK
  | ']' -> RBRACK
  | '{' -> LBRACE
  | '}' -> RBRACE
  | ':' -> COLON
  | '=' -> EQUALS
  | "..." -> DOTS
  | '.' -> DOT
  | ',' -> COMMA
  | ';' -> SEMI
  | '_' -> UNDER
  | '?' -> QUESTION
  | '&' -> AMPER
  | '|' -> VBAR
  | "->" -> ARROW
  | "<:" -> SUBTYPE
  | ":>" -> SUPTYPE

  | "fn" -> FN
  | "let" -> LET
  | "true" -> TRUE
  | "false" -> FALSE
  | "if" -> IF
  | "else" -> ELSE
  | "$outer" -> SHIFT
  | "as" -> AS

  | Plus('0'..'9') -> INT (int_of_string (lexeme buf))
  | ('a'..'z'|'A'..'Z'|'_'), Star('a'..'z'|'A'..'Z'|'0'..'9') ->
     SYMBOL (lexeme buf)
  | '@', Star('a'..'z') ->
     PRAGMA (sub_lexeme buf 1 (lexeme_length buf - 1))
  | eof -> EOF

  | any -> ERROR
  | _ -> ERROR


let token_name = function
  | WS -> "WS"
  | UNDER -> "UNDER"
  | TRUE -> "TRUE"
  | STRING _ -> "STRING"
  | SEMI -> "SEMI"
  | RPAR -> "RPAR"
  | RBRACK -> "RBRACK"
  | RBRACE -> "RBRACE"
  | QUESTION -> "QUESTION"
  | NL -> "NL"
  | LPAR -> "LPAR"
  | LET -> "LET"
  | LBRACK -> "LBRACK"
  | LBRACE -> "LBRACE"
  | INT _ -> "INT"
  | IF -> "IF"
  | SYMBOL _ -> "SYMBOL"
  | PRAGMA _ -> "PRAGMA"
  | DOTS -> "DOTS"
  | FN -> "FN"
  | FALSE -> "FALSE"
  | ERROR -> "ERROR"
  | EQUALS -> "EQUALS"
  | EOF -> "EOF"
  | ELSE -> "ELSE"
  | DOT -> "DOT"
  | COMMENT -> "COMMENT"
  | COMMA -> "COMMA"
  | COLON -> "COLON"
  | ARROW -> "ARROW"
  | AMPER -> "AMPER"
  | VBAR -> "VBAR"
  | SHIFT -> "SHIFT"
  | AS -> "AS"
  | SUBTYPE -> "SUBTYPE"
  | SUPTYPE -> "SUPTYPE"
