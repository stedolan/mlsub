type rawline = Comment of string | Input of string | Output of string | Empty

let rec rawlines acc =
  match input_line stdin with
  | exception End_of_file -> List.rev acc
  | s when String.length s = 0 -> rawlines (Empty :: acc)
  | s when s.[0] = '#' -> rawlines (Comment s :: acc)
  | s when s = ">" || (s.[0] = '>' && s.[1] = ' ') -> rawlines (Output s :: acc)
  | s -> rawlines (Input s :: acc)

type cmd = Comment of string | Input of string list

let rec parse_cmds acc curr : rawline list -> cmd list = function
  | [] -> List.rev (finish_cmd acc curr)
  | Empty :: rest ->
     (match curr with
      | [] -> parse_cmds (Comment "" :: acc) [] rest
      | c -> parse_cmds acc ("" :: c) rest)
  | Comment s :: rest ->
     parse_cmds (Comment s :: finish_cmd acc curr) [] rest
  | Output _ :: rest ->
     parse_cmds (finish_cmd acc curr) [] rest
  | Input s :: rest ->
     parse_cmds acc (s :: curr) rest
     
and finish_cmd acc curr : cmd list =
  match curr with [] -> acc | c -> Input (List.rev c) :: acc

let run_cmd s =
  let text = String.concat "\n" s in
  let open Lang in
  match Parse.parse_string text with
  | Ok e ->
     let env0 : Typedefs.env = { level = Typedefs.Env_level.empty;
                                 marker = Typedefs.Env_marker.make ();
                                 entry = Eflexible (Vector.create ());
                                 rest = None } in
     let flex0 = (env0.level, env0.marker) in
     (match Check.infer env0 flex0 e with
     | t ->
        let b = Buffer.create 100 in
        let open Typedefs in
(*        let rec as_styp pol = function
          | Tsimple t -> t
          | Tcons c -> cons_styp pol vsnil (map_head pol as_styp c)
          | _ -> raise Exit in
        let t = match as_styp Pos t with exception Exit -> t | s -> Tsimple (Type_simplification.garbage_collect env0 Pos s) in*)
        PPrint.ToBuffer.pretty 1. 80 b (PPrint.(group @@ group (string "*" ^^ Typedefs.pr_env env0) ^^ break 1 ^^ group (utf8string "⊢" ^^ break 1 ^^ (Typedefs.pr_typ Pos t))));
        b |> Buffer.to_bytes |> Bytes.to_string
     | exception ((Assert_failure _ | Types.Internal _) as e) ->
        Printexc.to_string e ^ "\n" ^ Printexc.get_backtrace ()
     | exception e ->
        "typechecking error: " ^ Printexc.to_string e)
  | Error _ -> "parse error"
  | exception (Failure s) -> "parser failure: " ^ s

let () =
  Printexc.record_backtrace true;
  let lines = rawlines [] in
  let cmds = parse_cmds [] [] lines in
  cmds |> List.iter (function
    | Comment s -> Printf.printf "%s\n" s
    | Input cmd ->
       List.iter (Printf.printf "%s\n") cmd;
       let out = run_cmd cmd in
       String.split_on_char '\n' out |> List.iter (Printf.printf "> %s\n"))
