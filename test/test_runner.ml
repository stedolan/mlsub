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
  let pexn = function
    | ((Assert_failure _ | Util.Internal _ | Out_of_memory | Invalid_argument _) as e) ->
       println "%s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
    | Error.Fail (loc, err) ->
       pprintln (Error.pp_err s loc err)
    | e ->
       println "typechecking error: %s" (Printexc.to_string e) in
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
     let check e =
       let fndef = None, [], None, e in
       let wrapped : Exp.exp = Some (Fn fndef), Location.noloc in
       match Check.infer Env.empty ~mode:(Check.fresh_gen_mode ()) wrapped with
       | Tcvj([Func ([], r), _], [], _),
         (Some (Fn (None, [], _, _, { act_body = rhs; _ })), _) ->  r, rhs
       | _ -> failwith "unexpected inference result (weak poly?)"
     in
     begin match check e with
     | t, etyped ->
        begin
        let elab = Elab.Elaborate.exp (Env.empty,[]) etyped in
        pprintln ~width:80 (PPrint.(nest 2 (blank 2 ^^ Print.exp elab)));

        let elab_rendered = to_string (Print.exp elab) in
        begin match Parse.parse_string elab_rendered with
        | exception e -> println "MISMATCH_ELAB: %s %s" (Printexc.to_string e) elab_rendered
        | Ok (`Exp elab') when Exp.equal elab elab' -> ()
        | Ok (`Exp elab') -> println "MISMATCH_ELAB: %s" (to_string ~width:100 (Print.exp elab'))
        | _ -> println "MISMATCH_ELAB"
        end;

        let env0 = Env.empty in
        let te = Typedefs.unparse_ptyp ~flexvar:ignore (*Env.empty*) t in
        pprintln (Print.tyexp te);
        begin try
          wf_ptyp env0 t;
          let t = Check.typ_of_tyexp env0 te in
          let env0 = env0 in
          Check.check env0 ~mode:(Check.fresh_gen_mode ()) e (Check.checking t) |> ignore
        with e ->
            println "RECHECK: %s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ());
            pexn e
        end;
        begin try
          wf_ptyp env0 t;
          let t = Check.typ_of_tyexp env0 te in
          let env0 = env0 in
          Check.check env0 ~mode:(Check.fresh_gen_mode ()) elab (Check.checking t) |> ignore
        with e ->
            println "ELAB: %s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
        end;
        begin try
          let t', _ty = check elab in
          let te' = Typedefs.unparse_ptyp ~flexvar:ignore t' in
          Types.subtype Env.empty t' (Check.typ_of_tyexp Env.empty te) |> Error.or_raise `Subtype Location.noloc;
          Types.subtype Env.empty t (Check.typ_of_tyexp Env.empty te') |> Error.or_raise `Subtype Location.noloc;
          ()
        with e ->
          println "ELABINF: %s\n%s" (Printexc.to_string e) (Printexc.get_backtrace ())
        end;
        begin
          let bcomp = Elab.Compile.exp etyped in
          let comp : IR.comp =
            Elab.IR_Builder.eval_cont bcomp (fun v -> Apply (Prim "yield", [v], [], Trap "done"))
          in
          IR.wf comp;
          let comp = IR.subst_aliases comp in
          IR.wf comp;
          pprintln ~width:80 (IR.pp comp);
        end;
        end
     | exception e ->
        pexn e
     end
  | Ok (`Prog p) ->
     let rendered = to_string (Print.prog p) in
     (* println "%s" rendered; *)
     begin match Parse.parse_string ("{ " ^  rendered ^ " }") with
     | exception e -> println "MISMATCH: %s" (Printexc.to_string e)
     | Ok (`Prog p') when Exp.equal_prog p p' -> ()
     | Ok (`Prog p') -> println "MISMATCH %s" (to_string ~width:1000 (Print.prog p'))
     | _ -> println "MISMATCH"
     end;
     begin match Check_decl.check_prog p with
     | env, decls -> List.iter (fun d -> pprintln (Print.decl (Check_decl.unparse_decl ~env d))) decls
     | exception e -> pexn e
     end
  | Ok (`Sub (t1, t2)) ->
     let module Env = Typedefs.Env in
     (match
       let t1 = Check.typ_of_tyexp Env.empty t1 in
       let t2 = Check.typ_of_tyexp Env.empty t2 in
       (*PPrint.(ToChannel.pretty 1. 80 stdout (Typedefs.pr_typ Pos t1 ^^ string " <: " ^^ Typedefs.pr_typ Neg t2 ^^ hardline));*)
       Types.subtype Env.empty t1 t2 |> Error.or_raise `Subtype Location.noloc
     with
      | () -> println "ok"
      | exception e -> pexn e)
  | Error _ -> println "parse error"
  | exception (Failure s) -> println "parser failure: %s" s
  end;
  Buffer.to_bytes outbuf |> Bytes.to_string

let () =
  Printexc.record_backtrace false;
  let lines = rawlines [] in
  let cmds = parse_cmds [] [] lines in
  Lang.Types.fixpoint_iters := 0;
  cmds |> List.iter (function
    | Comment s -> Printf.printf "%s\n" s
    | Input cmd ->
       List.iter (Printf.printf "%s\n") cmd;
       let out = run_cmd cmd in
       out |> String.trim |> String.split_on_char '\n' |> List.iter (Printf.printf "> %s\n"));
  Printf.printf "> STATS: fix: %d, flex: %d\n" !Lang.Types.fixpoint_iters !Lang.Typedefs.next_flexvar_id
