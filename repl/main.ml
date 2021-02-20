open Lang
open Typedefs
open Types
  
(*
open Parse
let app_name = "polytope"

let rec run_repl ~histfile () =
  Printf.printf "%!";
  match LNoise.linenoise "> " with
  | None -> ()
  | Some line ->
    LNoise.history_add line |> ignore;
    LNoise.history_save ~filename:histfile |> ignore;
    begin match Parse.parse_string line with
    | Ok e ->
       PPrint.ToChannel.pretty 1. 80 stdout
         (Print.print_exp e);
       Printf.printf "\n: %!";
       PPrint.ToChannel.pretty 1. 80 stdout
         (Typedefs.pr_typ Pos (Check.infer Check.env0 e));
       Printf.printf "\n%!"
    | Error _ -> raise (Fatal Unexpected_eof)
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
*)
