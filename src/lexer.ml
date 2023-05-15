open Grammar
open Sedlexing
open Sedlexing.Utf8
let rec lex buf =
  match%sedlex buf with
  | Plus(' ' | '\t') -> WS
  | '\n' | "\r\n" -> (* NL *) lex buf
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
  | '~' -> TILDE
  | "->" -> ARROW
  | "=>" -> FATARROW
  | "<:" -> SUBTYPE
  | ":>" -> SUPTYPE
  | '@' -> AT

  | "fn" -> FN
  | "let" -> LET
  | "true" -> TRUE
  | "false" -> FALSE
  | "if" -> IF
  | "else" -> ELSE
  | "$outer" -> SHIFT
  | "as" -> AS
  | "match" -> MATCH

  | Plus('0'..'9') -> INT (int_of_string (lexeme buf))
  | ('a'..'z'|'_'), Star('a'..'z'|'_'|'A'..'Z'|'0'..'9') ->
     SYMBOL (lexeme buf)
  | ('A'..'Z'), Star('a'..'z'|'_'|'A'..'Z'|'0'..'9') ->
     USYMBOL (lexeme buf)
  | '\'', ('A'..'Z'), Star('a'..'z'|'_'|'A'..'Z'|'0'..'9') ->
     QUSYMBOL (sub_lexeme buf 1 (lexeme_length buf - 1))

  | '@', Star('a'..'z') ->
     PRAGMA (sub_lexeme buf 1 (lexeme_length buf - 1))
  | eof -> EOF

  | any -> ERROR
  | _ -> ERROR
