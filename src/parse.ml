type lexeme = {
  token: Grammar.token;
  loc_start: Lexing.position;
  loc_end: Lexing.position;
}
type source = {
  name: string;
  source: string;
  tokens: lexeme list;
}

type error =
  | Mismatched_parens of lexeme option * lexeme option
  | Unexpected_eof
exception Fatal of error

type nest_type = File | Paren | Brace | Bracket

type lextree =
  | Tok of { token : Grammar.token; loc_start: Lexing.position; loc_end: Lexing.position }
  | Nest of { nest_type : nest_type; elems: lexforest } (* elems includes delimiters *)
and lexforest = lextree list

type token_class =
  | Tok_open of nest_type
  | Tok_close of nest_type
  | Tok_normal
let token_class : Grammar.token -> token_class = function
  | LPAR -> Tok_open Paren
  | RPAR -> Tok_close Paren
  | LBRACE -> Tok_open Brace
  | RBRACE -> Tok_close Brace
  | LBRACK -> Tok_open Bracket
  | RBRACK -> Tok_close Bracket
  | EOF -> Tok_close File
  | _ -> Tok_normal

let tok_open : nest_type -> Grammar.token list =
  function Paren -> [LPAR] | Brace -> [LBRACE] | Bracket -> [LBRACK] | File -> []
let tok_close : nest_type -> Grammar.token list =
  function Paren -> [RPAR] | Brace -> [RBRACE] | Bracket -> [RBRACK] | File -> [EOF]

let mkerror nest loc_start loc_end =
  let mktoks toks loc =
    List.map (fun token -> Tok {token; loc_start = loc; loc_end = loc}) toks in
  mktoks (tok_open nest) loc_start @ [Tok {token=ERROR; loc_start; loc_end}] @ mktoks (tok_close nest) loc_end

let rec scan lexbuf nest acc : lexforest =
  let token = Lexer.lex lexbuf in
  let (loc_start, loc_end) = Sedlexing.lexing_positions lexbuf in
  let tok = Tok { token; loc_start; loc_end } in
  match token_class token with
  | Tok_open nest_type ->
     let sub = Nest { nest_type; elems = scan lexbuf nest_type [tok] } in
     scan lexbuf nest (sub :: acc)
  | Tok_close ty when ty = nest ->
     List.rev (tok :: acc)
  | Tok_normal ->
     begin match nest, token with
     | _, WS
     | (Paren|Bracket), NL -> scan lexbuf nest acc
     | _ -> scan lexbuf nest (tok :: acc)
     end
  | Tok_close _ ->
     failwith "mismatched parens"

module P = Grammar.MenhirInterpreter

let rec parse p (toks : lexforest) =
  match toks with
  | [] -> Ok p
  | Tok { token; loc_start; loc_end } :: rest ->
     let input = (token, loc_start, loc_end) in
     let rec go = function
       (* Should never see Rejected, as we do not resume on HandlingError *)
       | P.Rejected -> assert false
       | (P.Shifting _ | P.AboutToReduce _) as p -> go (P.resume p)
       | (P.Accepted _ | P.InputNeeded _) as p -> parse p rest
       | P.HandlingError _ as p -> Error (input, p) in
     go (P.offer p input)
  | Nest { nest_type; elems } :: rest ->
     match parse p elems with
     | Ok p -> parse p rest
     | Error ((_tok, loc_start, loc_end), _) as orig_err ->
        match parse p (mkerror nest_type loc_start loc_end) with
        | Ok p -> parse p rest
        | Error _ -> orig_err

let parse_string s =
  let lexbuf = Sedlexing.Utf8.from_string s in
  let startpos = fst (Sedlexing.lexing_positions lexbuf) in
  let tokens = scan lexbuf File [] in
  match parse (Grammar.Incremental.prog startpos) tokens with
  | Ok (P.Accepted x) -> Ok x
  | Ok (P.InputNeeded _) -> failwith "unexpected eof"
  | _ -> failwith "bad parse"
