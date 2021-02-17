open Lang
open Typedefs
open Types


let dump t =
  let fvs = Hashtbl.create 20 in
  let fv_list = ref [] in
  let _name_ix = ref 0 in
  let names = [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "κ"; "ν"; "ξ"; "π"; "ρ" |] in
  let fresh_name fv =
    (*let id = !name_ix in
    incr name_ix;*)
    let id = fv.id in
    if id < Array.length names then names.(id)
    else Printf.sprintf "_%d" (id - Array.length names) in

  let rec styp_of_styp_neg = function
    | UBnone -> Scons Top
    | UBvar v -> Svar (Vflex v)
    | UBcons { cons; rigvars = [] } -> Scons cons
    | UBcons { cons; rigvars = v :: rigvars } ->
       Sjoin (styp_of_styp_neg (UBcons {cons; rigvars}),
              Svar (Vrigid v))
  in
  let rec flexvar fv =
    match Hashtbl.find fvs fv.id with
    | name, _ -> named_type name
    | exception Not_found ->
       let fv_name = fresh_name fv in
       Hashtbl.add fvs fv.id (fv_name, None);
       fv_list := fv.id :: !fv_list;
       let l =
         match fv.lower with
         | {cons=Bot; vars=[]} -> None
         | l -> Some (unparse (styp_of_flex_lower_bound l)) in
       let u =
         match fv.upper with
         | u -> Some (unparse (styp_of_styp_neg (map_styp_neg styp_flexvar u))) in
       Hashtbl.replace fvs fv.id (fv_name, Some (l, u));
       named_type fv_name
  and unparse t =
    unparse_styp ~flexvar t
  in
  let t = unparse t in
  let fvs = !fv_list |> List.rev |> List.map (fun i -> let (n, t) = (Hashtbl.find fvs i) in n, Option.get t) in
  let open PPrint in
  let doc =
    group (Print.tyexp t) ^^ hardline ^^
    utf8string "where" ^^ hardline ^^
    nest 2 (blank 2 ^^ separate_map hardline (fun (n, (l, u)) -> group @@ 
      (match l with
       | None -> empty
       | Some l -> Print.tyexp l ^^ blank 1 ^^ utf8string "<:" ^^ blank 1)
      ^^
      utf8string n
      ^^
      (match u with
       | None -> empty
       | Some u -> blank 1 ^^ utf8string "<:" ^^ blank 1 ^^ Print.tyexp u))
          fvs) ^^ hardline in
  PPrint.ToChannel.pretty 1. 120 stdout doc

let func a b = Func (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) a)), b)

let tuple xs = Record (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) xs)))

(*
let () = 
  let env = Env_nil in
  let lvl = Env_level.initial () in
  let error _ = failwith "nope" in
  let a = fresh_flexvar lvl in
  let b = fresh_flexvar lvl in
  let c = fresh_flexvar lvl in
  let d = fresh_flexvar lvl in
  let e = fresh_flexvar lvl in
  let f = fresh_flexvar lvl in
  let st p q = subtype_styp ~error env (styp_flexvar p) (UBvar q) in
  let stcons p c = subtype_styp ~error env (styp_flexvar p) (UBcons {cons=c;rigvars=[]}) in
  st a b;
  st d e;
  stcons c Int;
  st c d;
  st e f;
  stcons e (func (styp_flexvar a) (styp_flexvar b));
  stcons e (func (styp_flexvar c) (styp_flexvar d));
  st b c;
  dump (sjoin (styp_flexvar a) (styp_flexvar f));
  stcons e (func (styp_flexvar c) (styp_flexvar d));
  dump (sjoin (styp_flexvar a) (styp_flexvar f))
*)

(* λ f, g, x . f x or g x *)
let choosy () =
  let env =  Env_nil and lvl = Env_level.initial () in
  let error _ = failwith "nope" in
  let f = fresh_flexvar lvl |> styp_flexvar in
  let g = fresh_flexvar lvl |> styp_flexvar in
  let x = fresh_flexvar lvl |> styp_flexvar in
  let res = fresh_flexvar lvl |> styp_flexvar in
  let apply f x =
    let argp, arg = Ivar.make () in
    let resp, res = Ivar.make () in
    match_styp ~error env f (func [argp] resp);
    subtype_styp ~error env x (Ivar.get arg);
    Ivar.get res in
  let fx = apply f x in
  let gx = apply g x in
  subtype_styp ~error env fx res;
  subtype_styp ~error env gx res;
  dump (styp_cons (func [f;g;x] res))

let lbs () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial () in
  let error _ = failwith "nope" in
  let f = fresh_flexvar lvl |> styp_flexvar in
  let d1 = fresh_flexvar lvl |> styp_flexvar in
  let d2 = fresh_flexvar lvl |> styp_flexvar in
  let r1 = fresh_flexvar lvl |> styp_flexvar in
  let r1' = fresh_flexvar lvl |> styp_flexvar in
  let r2 = fresh_flexvar lvl |> styp_flexvar in
  subtype_styp ~error env r1 r1';
  subtype_styp ~error env (Scons (func [d1] r1)) f;
  subtype_styp ~error env (Scons (func [d2] r2)) f;
  dump (styp_cons (func [r1;r2;r1'] (styp_cons (tuple [f;d1;d2]))))


let () = choosy ()
let () = lbs ()
  
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
