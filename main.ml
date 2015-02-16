open Lexer
open Lexing

open Printf

let parse_line f g =
  try g (f Lexer.read (Lexing.from_string (input_line stdin))) with
  | SyntaxError _ -> fprintf stderr "syntax error\n%!"
  | Parser.Error -> fprintf stderr "parser error\n%!"
;;

open Types;;
open Typecheck;;

(*
let automaton = (constrain (compile_terms (fun f ->
    [f Neg (TVar "x"), TVar "a"; 
     f Pos (TVar "x"), TVar "b"]))
     Pos (TCons (Func (TVar "a", TVar "b"))));;
Format.printf "%a\n%a\n%!" (print_typeterm Pos) (decompile_automaton automaton) print_automaton automaton
*)
  
(*
parse_line Parser.prog (fun s -> 
parse_line Parser.onlytype (fun t ->
  let s1 = s.Typecheck.expr in
  let s2 = compile_terms (fun f -> f Pos t) in
  expand_all_flow s1;
  expand_all_flow s2;
    Format.printf "%a\n%a\n%!"
      print_automaton s1
      print_automaton s2;
    let sub s1 s2 = 
      Format.printf "%a <: %a [%s]\n%!"
        (print_typeterm Pos) (decompile_automaton s1) 
        (print_typeterm Pos) (decompile_automaton s2)
        (match subsumed (fun f -> f s1 s2) with true -> "Y" | false -> "N") in
    sub s1 s2; sub s2 s1))
;;  
*)

  (*
while true do
  parse_line Parser.subsumption (fun (t1, t2) ->
    let s1 = compile_terms (fun f -> f Pos t1)
    and s2 = compile_terms (fun f -> f Pos t2) in
    Format.printf "%a\n%a\n%!"
      print_automaton s1
      print_automaton s2;
    let sub s1 s2 = 
      Format.printf "%a <: %a [%s]\n%!"
        (print_typeterm Pos) (decompile_automaton s1) 
        (print_typeterm Pos) (decompile_automaton s2)
        (match subsumed (fun f -> f s1 s2) with true -> "Y" | false -> "N") in
    sub s1 s2; sub s2 s1)
done

   *)

let run exp =
  let (name, chan) = Filename.open_temp_file ~mode:[Open_wronly] "tmp" "ml" in
  Camlgen.to_caml (Format.formatter_of_out_channel chan) exp;
  close_out chan;
  ignore (Sys.command ("cat "^name ^"; ocaml " ^ name));
  Sys.remove name

let gamma0 = SMap.singleton (Symbol.intern "p") 
   { environment = SMap.empty;
     expr = (compile_terms 
       (fun f -> f Pos (ty_fun (ty_base (Symbol.intern "int")) 
                               (ty_base (Symbol.intern "unit"))))) }

;;

while true do
  let recomp s = decompile_automaton (compile_terms (fun f -> f Pos (decompile_automaton s))) in
  parse_line Parser.prog
             (fun exp ->
              (try
                let s = Typecheck.typecheck gamma0 exp in
                (*                Format.printf "%a\n%!" (print_typeterm Pos) (decompile_automaton s.Typecheck.expr); *)
                Format.printf "%a\n%!" (print_typeterm Pos) (recomp s.Typecheck.expr)
              with
              | Failure msg -> Format.printf "Typechecking failed: %s\n%!" msg
              | Not_found -> Format.printf "Typechecking failed: Not_found\n%!"
              | Match_failure (file, line, col) -> Format.printf "Match failure in typechecker at %s:%d%d\n%!" file line col);
              run exp )
  (*parse_line Parser.prog (fun s -> Format.printf "%a\n%!" print_automaton s.Typecheck.expr)*)
done



(*

while true do
  parse_line Parser.onlytype (fun t -> Format.printf "%a\n%!" (print_typeterm Pos) t)
done

*)

(*
let parse_with_error lexbuf =
  try Some (Parser.prog Lexer.read lexbuf) with
  | SyntaxError _ | Parser.Error ->
    fprintf stderr "nope\n%!"; None

(* part 1 *)
let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    printf "%s\n%!" value
  | None -> ();;

while true do
  parse_and_print (Lexing.from_string (input_line stdin))
done
*)

(*
let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx

(* part 2 *)
let () =
  Command.basic ~summary:"Parse and display JSON"
    Command.Spec.(empty +> anon ("filename" %: file))
    loop 
  |> Command.run
*)
