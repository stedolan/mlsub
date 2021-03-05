open Lang
open Typedefs
open Types
module SymMap = Tuple_fields.SymMap

let dump (t : ptyp) =
  let fvs = Hashtbl.create 20 in
  let fv_list = ref [] in
  let _name_ix = ref 0 in
  let rec flexvar fv =
    match Hashtbl.find fvs fv.id with
    | _ -> ()
    | exception Not_found ->
       let fv_name = flexvar_name fv in
       Hashtbl.add fvs fv.id (fv_name, None);
       fv_list := fv.id :: !fv_list;
       let l =
         match fv.lower with
         | {ctor={cons=Bot; rigvars=[]}; flexvars=[]} -> None
         | l -> Some (unparse_flex_lower_bound ~flexvar l) in
       let u =
         match fv.upper with
         | UBvar v -> unparse_flexvar ~flexvar v
         | UBnone -> unparse (Tcons Top)
         | UBcons {cons;rigvars} ->
            let cons = unparse_cons ~neg:(unparse_flex_lower_bound ~flexvar) ~pos:(unparse_flexvar ~flexvar) cons in
            unparse_join cons rigvars in
       Hashtbl.replace fvs fv.id (fv_name, Some (l, u));
       ()
  and unparse t =
    unparse_ptyp ~flexvar t
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
       | Some l -> Print.tyexp l ^^ blank 1 ^^ utf8string "≤" ^^ blank 1)
      ^^
      utf8string n
      ^^
      (blank 1 ^^ utf8string "≤" ^^ blank 1 ^^ Print.tyexp u))
          fvs) ^^ hardline in
  PPrint.ToChannel.pretty 1. 120 stdout doc

let func a b = Func (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) a)), b)

let tuple xs = Record (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) xs)))

let nope _ = assert false

let dump env level (t : ptyp) =
  dump t;
  let fl = approx_ptyp env t in
  let changes = ref [] in
  let fl = expand 2 ~changes env level fl in
  Printf.printf "changed: %b\n" (!changes <> []);
  dump (Tsimple fl);
  if !changes <> [] then begin
  let changes = ref [] in
  let fl = expand 4 ~changes env level fl in
  Printf.printf "changed: %b\n" (!changes <> []);
  dump (Tsimple fl);

  let bvars = Vector.create () in
  let fl = substn 4 bvars level ~index:0 fl in
  dump fl;
  Vector.iteri bvars (fun ix v -> match v with
  | Gen_rigid _ -> assert false
  | Gen_flex (_, r) ->
    PPrint.ToChannel.pretty 1. 120 stdout PPrint.(utf8string (Printf.sprintf "  $%d ≤ " ix) ^^ group (Print.tyexp (unparse_ntyp ~flexvar:nope !r)) ^^ hardline));
  end;
  print_endline ""

let fresh_flow lvl =
  let fv = fresh_flexvar lvl in
(*  Tsimple fv, Tsimple (flexlb_fv fv)*)
  Tvar (Vflex fv), Tvar (Vflex fv)


(* λ f, g, x . f x or g x *)
let choosy () =
  let env =  Env_nil and lvl = Env_level.initial in
  let error _ = failwith "nope" in
  let fn, fp = fresh_flow lvl in
  let gn, gp = fresh_flow lvl in
  let xn, xp = fresh_flow lvl in
  let resn, resp = fresh_flow lvl in
  let apply f x =
    let argp, arg = Ivar.make () in
    let resp, res = Ivar.make () in
    match_typ ~error env lvl f (func [argp] resp);
    subtype ~error env x (Ivar.get arg);
    Ivar.get res in
  let fx = apply fp xp in
  let gx = apply gp xp in
  subtype ~error env fx resn;
  subtype ~error env gx resn;
  let ty = Tcons (func [fn;gn;xn] resp) in
  dump env lvl ty
(*
  let root = gen env lvl ty in
  dump (styp_of_flex_lower_bound root.lower);
  dump (gen_subst env lvl root)
*)           

let lbs () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let error _ = failwith "nope" in
  let fn, fp = fresh_flow lvl in
  let d1n, d1p = fresh_flow lvl in
  let d2n, d2p = fresh_flow lvl in
  let r1n, r1p = fresh_flow lvl in
  let r1'n, _r1'p = fresh_flow lvl in
  let r2n, r2p = fresh_flow lvl in
  subtype ~error env r1p r1'n;
  subtype ~error env (Tcons (func [d1n] r1p)) fn;
  subtype ~error env (Tcons (func [d2n] r2p)) fn;
  let ty = (Tcons (func [r1n;r2n] (Tcons (tuple [fp;d1p;d2p])))) in
  dump env lvl ty

let match_as_fn ~error env lvl f =
  let argp, arg = Ivar.make () in
  let resp, res = Ivar.make () in
  match_typ ~error env lvl f (func [argp] resp);
  Ivar.get arg, Ivar.get res


let match_bug () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let error _ = failwith "nope" in
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  subtype ~error env ap bn;
  let b1, b2 = match_as_fn ~error env lvl bp in
  let a1, a2 = match_as_fn ~error env lvl ap in
  subtype ~error env a2 (Tcons Bot);
  dump env lvl (Tcons (func [a1; b1; an] (Tcons (tuple [a2; b2; bp]))))
  

let chain () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let error _ = failwith "nope" in
  let a = Array.init 10 (fun _ -> fresh_flow lvl) in
  let n = Array.map fst a and p = Array.map snd a in
  subtype ~error env p.(5) (Tcons Top);
  subtype ~error env p.(4) n.(5);
  subtype ~error env p.(3) n.(4);
  subtype ~error env p.(8) n.(9);
  subtype ~error env p.(5) n.(6);
  subtype ~error env p.(0) n.(1);
  subtype ~error env p.(3) (Tcons Top);
  subtype ~error env p.(2) n.(3);
  subtype ~error env p.(1) n.(2);
  subtype ~error env p.(7) n.(8);
  subtype ~error env p.(6) n.(7);
  dump env lvl (Tcons (func [n.(0)] p.(9)))

let dirbug () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let error _ = failwith "nope" in
  let an, _ap = fresh_flow lvl in
  let _bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  let dn, dp = fresh_flow lvl in
  subtype ~error env (Tcons (func [an] bp)) (Tcons (func [cp] dn));
  dump env lvl (Tcons (tuple [Tcons (func [an] bp); Tcons (func [cn] dp)]))

let poly () =
  next_flexvar_id := 0;
  let env = Env_nil and _lvl = Env_level.initial in
  let error _ = failwith "nope" in
  let bvar ?(index=0) ?(rest) var =
    match rest with
    | None -> Tvar (Vbound {index; var})
    | Some rest -> Tvjoin (rest, Vbound{index; var}) in
  let t1 () =
    Tpoly {vars = IArray.of_array [| "A", Tcons Top; "B", Tcons Top |];
           body= Tcons (func
                   [bvar 0]
                   (Tcons (func
                     [bvar 1]
                     (bvar 1 ~rest:(bvar 0))))) } in
  let t2 () =
    Tpoly {vars = IArray.of_array [| "X", Tcons Top |];
           body = Tcons (func [bvar 0] (Tcons (func [bvar 0] (bvar 0))))} in
  let t3 () =
    Tpoly {vars = IArray.of_array [| "P", Tcons Top |];
           body = Tcons (func [bvar 0] (
             Tpoly {vars=IArray.of_array [| "Q", Tcons Top |];
                    body = Tcons (func [bvar 0] (bvar ~rest:(bvar ~index:1 0) 0))}))} in
  print_endline "t1 = t2";
  subtype ~error env (t1 ()) (t2 ());
  subtype ~error env (t2 ()) (t1 ());
  print_endline "t3 <= t1, t2";
  subtype ~error env (t3 ()) (t2 ());
  subtype ~error env (t3 ()) (t1 ());
  let sub = ref true in
  subtype ~error:(fun _ -> sub := false) env (t1 ()) (t3 ());
  Printf.printf "t1 <= t3: %b\n" !sub;
            
(*  subtype ~error env (t2 ()) (t3 ());*)
  ()

let () = choosy ()
let () = lbs ()
let () = match_bug ()
let () = chain ()
let () = dirbug ()
let () = poly ()
