type rawline = Comment of string | Input of string | Output of string | Empty

let rec rawlines acc =
  match input_line stdin with
  | exception End_of_file -> List.rev acc
  | s when String.length s = 0 -> rawlines (Empty :: acc)
  | s when s.[0] = '#' -> rawlines (Comment s :: acc)
  | s when s = ">" || (s.[0] = '>' && s.[1] = ' ') -> rawlines (Output s :: acc)
  | s -> rawlines (Input s :: acc)

type cmd = Comment of string | Input of string list

let to_string ?(width=80) doc =
  let b = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. width b (PPrint.group doc);
  b |> Buffer.to_bytes |> Bytes.to_string

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
  let outbuf = Buffer.create 100 in
  let println fmt =
    Printf.ksprintf (fun s ->
      Buffer.add_string outbuf s; Buffer.add_char outbuf '\n') fmt in
  let pprintln ?(width=120) d =
    PPrint.ToBuffer.pretty 1. width outbuf PPrint.(PPrint.group d ^^ hardline) in
  begin match Parse.parse_string text with
  | Ok (`Exp e) ->
     let rendered = to_string (Print.exp e) in
     println "%s" rendered;
     begin match Parse.parse_string rendered with
      | exception e -> println "MISMATCH: %s" (Printexc.to_string e)
      | Ok (`Exp e') when Exp.equal e e' -> ()
      | Ok (`Exp e') -> println "MISMATCH %s" (to_string ~width:1000 (Print.exp e'))
      | _ -> println "MISMATCH"
     end;
     let open Typedefs in
     begin match Check.elab_gen Env_nil None (fun env -> Check.infer env e) with
     | t, elab ->
        begin
        let poly, _ty, elab = Elab.elaborate Env_nil elab in
        let elab = Exp.(map_exp normalise elab) in
        poly |> Option.iter (fun poly ->
          pprintln PPrint.(string "WEAKPOLY" ^^ Print.typolybounds poly));
        pprintln ~width:80 (PPrint.(nest 2 (blank 2 ^^ Print.exp elab)));

        let elab_rendered = to_string (Print.exp elab) in
        begin match Parse.parse_string elab_rendered with
        | exception e -> println "MISMATCH_ELAB: %s" (Printexc.to_string e)
        | Ok (`Exp elab') when Exp.equal elab elab' -> ()
        | Ok (`Exp elab') -> println "MISMATCH_ELAB: %s" (to_string ~width:100 (Print.exp elab'))
        | _ -> println "MISMATCH_ELAB"
        end;

        let env0 = Env_nil in
        let te = Typedefs.unparse_ptyp ~flexvar:ignore (*Env_nil*) t in
        pprintln (Print.tyexp (Exp.(map_tyexp normalise te)));
        begin try
          wf_ptyp env0 t;
          let t = Check.typ_of_tyexp env0 te in
          let env0 = env0 in
          Check.check env0 e t |> ignore
        with e ->
            println "RECHECK: %s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
        end;
        begin try
          wf_ptyp env0 t;
          let t = Check.typ_of_tyexp env0 te in
          let env0 = env0 in
          Check.check env0 elab t |> ignore
        with e ->
            println "ELAB: %s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
        end;
        begin try
          let t', _elab2 = Check.elab_gen Env_nil None (fun env -> Check.infer env elab) in
          let te' = Typedefs.unparse_ptyp ~flexvar:ignore t' in
          Types.subtype ~error:Check.report Env_nil t' (Check.typ_of_tyexp Env_nil te);
          Types.subtype ~error:Check.report Env_nil t (Check.typ_of_tyexp Env_nil te');
          ()
        with e ->
          println "ELABINF: %s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
        end;
        end
     | exception ((Assert_failure _ | Typedefs.Internal _ | Out_of_memory | Invalid_argument _) as e) ->
        println "%s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
     | exception e ->
        println "typechecking error: %s" (Printexc.to_string e)
     end
  | Ok (`Sub (t1, t2)) ->
     (match
       let t1 = Check.typ_of_tyexp Env_nil t1 in
       let t2 = Check.typ_of_tyexp Env_nil t2 in
       (*PPrint.(ToChannel.pretty 1. 80 stdout (Typedefs.pr_typ Pos t1 ^^ string " <: " ^^ Typedefs.pr_typ Neg t2 ^^ hardline));*)
       Types.subtype ~error:Check.report Env_nil t1 t2
     with
      | () -> println "ok"
      | exception ((Assert_failure _ | Typedefs.Internal _ | Stack_overflow) as e) ->
         println "exception: %s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
      | exception e -> println "typechecking error: %s" (Printexc.to_string e))
  | Error _ -> println "parse error"
  | exception (Failure s) -> println "parser failure: %s" s
  end;
  Buffer.to_bytes outbuf |> Bytes.to_string

let () =
  Printexc.record_backtrace true;
  let lines = rawlines [] in
  let cmds = parse_cmds [] [] lines in
  cmds |> List.iter (function
    | Comment s -> Printf.printf "%s\n" s
    | Input cmd ->
       List.iter (Printf.printf "%s\n") cmd;
       let out = run_cmd cmd in
       out |> String.trim |> String.split_on_char '\n' |> List.iter (Printf.printf "> %s\n"))
