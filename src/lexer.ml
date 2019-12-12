open Parser
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
  | '.' -> DOT
  | ',' -> COMMA
  | ';' -> SEMI
  | '_' -> UNDER
  | '?' -> QUESTION
  | '&' -> AMPER
  | '|' -> VBAR
  | "->" -> ARROW

  | "fn" -> FN
  | "let" -> LET
  | "true" -> TRUE
  | "false" -> FALSE
  | "if" -> IF
  | "else" -> ELSE
  | "$outer" -> SHIFT

  | Plus('0'..'9') -> INT (int_of_string (lexeme buf))
  | ('a'..'z'|'A'..'Z'|'_'), Star('a'..'z'|'A'..'Z'|'0'..'9') ->
     SYMBOL (lexeme buf)
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
