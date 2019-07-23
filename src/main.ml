type lexeme = {
  token: Parser.token;
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

open Parser
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
  Exp.exp MenhirInterpreter.checkpoint
type state =
  (lexeme * checkpoint) list

module P = Parser.MenhirInterpreter

let feed_parser (p : checkpoint) tok =
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

let rec parse (s : state) p (tokens : lexeme list) =
  match tokens with
  | [] -> s, p
  | tok :: tokens when not (tok_significant s tok.token) ->
     parse s p tokens
  | tok :: tokens ->
     match feed_parser p tok with
     | Ok p ->
        parse (advance s p tok) p tokens
     | Error _ ->
        failwith "plz recover"


let app_name = "polytope"

let rec run_repl ~histfile () =
  Printf.printf "%!";
  match LNoise.linenoise "> " with
  | None -> ()
  | Some line ->
    LNoise.history_add line |> ignore;
    LNoise.history_save ~filename:histfile |> ignore;
    let lexbuf = Utf8.from_string line in
    let startpos = fst (lexing_positions lexbuf) in
    let tokens = scan lexbuf [] in
    let source = { name = "<stdin>"; source = line; tokens } in
    dump_tokens source;
    let p = Parser.Incremental.prog startpos in
    begin match parse [] p tokens with
    | [], p ->
       begin match finish_parser p with
       | Ok e ->
          PPrint.ToChannel.pretty 1. 80 stdout
            (Print.print_exp e);
          Printf.printf "\n%!"
       | Error _ -> raise (Fatal Unexpected_eof)
       end
    | _, _ -> Printf.printf "??\n"
    end;
    run_repl ~histfile ()
  
let () =
  let histfile =
    XDGBaseDir.default.data_home
    ^ Filename.dir_sep ^ app_name
    ^ Filename.dir_sep ^ "history" in
  histfile |> XDGBaseDir.mkdir_openfile (fun histfile ->
    LNoise.history_load ~filename:histfile |> ignore;
    LNoise.history_set ~max_length:1000 |> ignore;
    run_repl ~histfile ())
