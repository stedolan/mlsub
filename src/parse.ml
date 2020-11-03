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


open Sedlexing
let rec scan lexbuf acc =
  match Lexer.lex lexbuf with
  | EOF -> List.rev acc
  | t ->
     let (loc_start, loc_end) = lexing_positions lexbuf in
     let token = { token = t; loc_start; loc_end } in
     scan lexbuf (token :: acc)

let dump_tokens { name; source; tokens } =
  Printf.printf "%s:\n" name;
  tokens |> List.iter (fun { token; loc_start; loc_end } ->
    Printf.printf "%8s: [%s]\n"
      (Lexer.token_name token)
      (String.sub source loc_start.pos_cnum
         (loc_end.pos_cnum - loc_start.pos_cnum)))

open Grammar
let tok_matches s t =
  match s, t with
  | LPAR, RPAR
  | LBRACE, RBRACE
  | LBRACK, RBRACK -> true
  | _, _ -> false

let tok_opens  = function LPAR | LBRACE | LBRACK -> true | _ -> false
let tok_closes = function RPAR | RBRACE | RBRACK -> true | _ -> false

let tok_significant s t =
  match s, t with
  | _, WS -> false
  | ([] | ({token = LBRACE; _}, _) :: _), NL -> true
  | _, NL -> false
  | _, _ -> true

type checkpoint =
  [`Exp of Exp.exp | `Sub of Exp.tyexp * Exp.tyexp] MenhirInterpreter.checkpoint
type state =
  (lexeme * checkpoint) list

module P = Grammar.MenhirInterpreter

let feed_token (p : checkpoint) tok =
  assert (tok.token <> EOF);
  let rec go = function
    (* Should never see Rejected, as we do not resume on HandlingError *)
    | P.Rejected -> assert false
    (* Should never see Accepted, as we have not input EOF yet *)
    | P.Accepted _ -> assert false
    | P.Shifting _
    | P.AboutToReduce _ as p -> go (P.resume p)
    | P.InputNeeded _ as p -> Ok p
    | P.HandlingError _ as p -> Error p in
  let input = (tok.token, tok.loc_start, tok.loc_end) in
  go (P.offer p input)

let finish_parser (p : checkpoint) =
  let eof_position =
    Lexing.{pos_fname="EOF"; pos_lnum=0; pos_cnum=0; pos_bol=0} in
  let rec go = function
    | P.Accepted e -> Ok e
    | P.Rejected -> assert false
    | P.Shifting _
    | P.AboutToReduce _ as p -> go (P.resume p)
    | P.InputNeeded _
    | P.HandlingError _ as p -> Error p in
  go (P.offer p (EOF, eof_position, eof_position))


let advance (s : state) p (tok : lexeme) =
  match s, tok.token with
  | [], t when tok_closes t ->
     raise (Fatal (Mismatched_parens (None, Some tok)))
  | ((op, _) :: s), t when tok_closes t ->
     if tok_matches op.token t then s else
       raise (Fatal (Mismatched_parens (Some op, Some tok)))
  | s, t when tok_opens t ->
      (tok, p) :: s
  | s, _ -> s

let rec feed_parser (s : state) p (tokens : lexeme list) =
  match tokens with
  | [] -> s, p
  | tok :: tokens when not (tok_significant s tok.token) ->
     feed_parser s p tokens
  | tok :: tokens ->
     match feed_token p tok with
     | Ok p ->
        feed_parser (advance s p tok) p tokens
     | Error _ ->
        failwith "plz recover"

let parse_string s =
  let lexbuf = Utf8.from_string s in
  let startpos = fst (lexing_positions lexbuf) in
  let tokens = scan lexbuf [] in
  let source = { name = "<stdin>"; source = s; tokens } in
  if false then dump_tokens source;
  let p = Grammar.Incremental.prog startpos in
  begin match feed_parser [] p tokens with
  | [], p -> finish_parser p
  | _ -> failwith "??"
  end
