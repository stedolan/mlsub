open Lang
open Typedefs
open Types
module SymMap = Tuple_fields.SymMap

let dump (t : ptyp) =
  Format.printf "%a%!" dump_ptyp t

let func a b = Func (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) a)), b)

let tuple xs = Record (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) xs)))

let nope _ = assert false

let pp_changes ppf changes =
  Printf.fprintf ppf "[";
  List.rev changes |> List.iteri (fun i ch ->
    let fv,ty =
      match ch with
      | Change_upper(v,_) -> v, "-"
      | Change_lower(v,_) -> v, "+"
      | Change_level(v,_) -> v, "@" in
    Printf.fprintf ppf "%s%s%s" (if i = 0 then "" else " ") (flexvar_name fv) ty);
  Printf.fprintf ppf "]"

let dump env level (t : ptyp) =
  dump t;
  flush stdout;
  let fl = approx_ptyp env t in
  let rec fixpoint visit fl =
    let changes = ref [] in
    let fl = expand visit ~changes env level fl in
    Printf.printf "changed: %a\n" pp_changes !changes;
    dump (Tsimple fl);
    if !changes = [] then visit, fl
    else fixpoint (visit + 2) fl in
  let visit, fl = fixpoint 2 fl in

  let bvars = Vector.create () in
  let fl = substn visit bvars level ~index:0 fl in
  dump fl;
  Vector.iteri bvars (fun ix v -> match v with
  | Gen_rigid _ -> assert false
  | Gen_flex (_, r) ->
    PPrint.ToChannel.pretty 1. 120 stdout PPrint.(utf8string (Printf.sprintf "  $%d ≤ " ix) ^^ group (Print.tyexp (unparse_ntyp ~flexvar:nope !r)) ^^ hardline));
  print_endline ""

let fresh_flow lvl =
  let fv = fresh_flexvar lvl in
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

let flexself () =
  let env = Env_nil and lvl = Env_level.initial in

  (* UBvar optimisation *)
  next_flexvar_id := 0;
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  let error _ = failwith "nope" in
  subtype ~error env ap bn;
  subtype ~error env bp cn;
  subtype ~error env ap cn;
  dump env lvl (Tcons (func [an] cp));

  (* Attempted UBvar recursion (should become UBcons) *)
  next_flexvar_id := 0;
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  let error _ = failwith "nope" in
  subtype ~error env ap bn;
  subtype ~error env bp cn;
  subtype ~error env cp an;
  dump env lvl ap;

  (* UBcons recursion, multiple steps to fixed point *)
  next_flexvar_id := 0;
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  subtype ~error env (Tcons Int) cn;
  subtype ~error env bp an;
  subtype ~error env cp an;
  subtype ~error env ap bn;
  dump env lvl ap

let () = choosy ()
let () = lbs ()
let () = match_bug ()
let () = chain ()
let () = dirbug ()
let () = poly ()
let () = flexself ()
