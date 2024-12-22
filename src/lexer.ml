open Grammar
open Sedlexing
open Sedlexing.Utf8

let chop s = String.sub s 1 (String.length s - 1)

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
  | ',' -> COMMA
  | ';' -> SEMI
  | '_' -> UNDER
  | '?' -> QUESTION
  | '&' -> AMPER
  | '|' -> VBAR
  | '~' -> TILDE
  | '#' -> HASH
  | "->" -> ARROW
  | "=>" -> FATARROW
  | "<:" -> SUBTYPE
  | ":>" -> SUPTYPE
  | '@' -> AT
  | '+' -> PLUS
  | '-' -> MINUS

  | "fn" -> FN
  | "let" -> LET
  | "true" -> TRUE
  | "false" -> FALSE
  | "if" -> IF
  | "else" -> ELSE
  | "$outer" -> SHIFT
  | "match" -> MATCH
  | "type" -> TYPE
  | "absent" -> ABSENT

  | "Any" -> T_ANY
  | "Nothing" -> T_NOTHING

  | '0' -> ZERO
  | Plus('0'..'9') -> NZINT (int_of_string (lexeme buf))
  | ('a'..'z'|'_'), Star('a'..'z'|'_'|'A'..'Z'|'0'..'9') ->
     SYMBOL (lexeme buf)
  | ('A'..'Z'), Star('a'..'z'|'_'|'A'..'Z'|'0'..'9') ->
     USYMBOL (lexeme buf)

  | '.', ('a'..'z'|'_'), Star('a'..'z'|'_'|'A'..'Z'|'0'..'9') ->
     DOT_SYMBOL (chop (lexeme buf))
  | '.', ('A'..'Z'), Star('a'..'z'|'_'|'A'..'Z'|'0'..'9') ->
     DOT_USYMBOL (chop (lexeme buf))
  | '.', ('0'..'9'), Star('0'..'9') ->
     DOT_INT (int_of_string (chop (lexeme buf)))

  | '@', Star('a'..'z') ->
     PRAGMA (sub_lexeme buf 1 (lexeme_length buf - 1))
  | eof -> EOF

  | any -> ERROR
  | _ -> ERROR
