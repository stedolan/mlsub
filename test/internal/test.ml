open Lang
open Util
open Typedefs
open Types
module SymMap = Tuple_fields.SymMap

let () = Printexc.record_backtrace true

let dump (t : ptyp) =
  Format.printf "%a%!" dump_ptyp t

let func a b = Cons.Func (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) a)), b)

let tuple xs = Cons.Record (Tuple_fields.(collect_fields (List.map (fun x -> Fpos x) xs)))

let nope _ = assert false

let dump env (t : ptyp) =
  dump t;
  flush stdout;
  let fl = ptyp_to_lower ~simple:false env t in
  let rec fixpoint visit fl =
    let changes = ref [] in
    let fl = expand_lower visit ~changes env fl in
    Format.printf "changed: %a\n" pp_changes !changes;
    dump (Tsimple fl);
    if !changes = [] then visit, fl
    else fixpoint (visit + 2) fl in
  let visit, fl = fixpoint 2 fl in

  let bvars = Vector.create () in
  let fl = promote_lower {mode=`Poly;visit; policy=Policy_generalise; bvars; env; level=env_level env; index=0} fl in
  dump (gen_zero fl);
  Vector.iteri bvars (fun ix v -> match v with
  | Gen_rigid _ -> assert false
  | Gen_flex r ->
    PPrint.ToChannel.pretty 1. 120 stdout PPrint.(utf8string (Printf.sprintf "  $%d ≤ " ix) ^^ group (Print.tyexp (unparse_ntyp ~flexvar:nope r)) ^^ hardline));
  print_endline ""

let fresh_flow lvl =
  let fv = fresh_flexvar lvl in
  Tsimple fv, Tsimple (of_flexvar fv)


let match_as_fn env f =
  let ((), arg), ((), res) =
    match_typ env f Location.noloc (func [()] ())
    |> function Ok (Func (a, r)) -> Tuple_fields.(FieldMap.find (Field_positional 0) a.fields), r 
              | _ -> assert false in
  arg, res

let tcons cons = Tcons (Cons.make ~loc:Location.noloc cons)

let ok = function Ok () -> () | Error _ -> failwith "nope"

(* λ f, g, x . f x or g x *)
let choosy () =
  let env =  Env_nil and lvl = Env_level.initial in
  let fn, fp = fresh_flow lvl in
  let gn, gp = fresh_flow lvl in
  let xn, xp = fresh_flow lvl in
  let resn, resp = fresh_flow lvl in
  let apply f x =
    let arg, res = match_as_fn env f in
    subtype env x arg |> ok;
    res in
  let fx = apply fp xp in
  let gx = apply gp xp in
  subtype env fx resn |> ok;
  subtype env gx resn |> ok;
  let ty = tcons (func [fn;gn;xn] resp) in
  dump env ty
(*
  let root = gen env lvl ty in
  dump (styp_of_flex_lower_bound root.lower);
  dump (gen_subst env lvl root)
*)           

let lbs () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let fn, fp = fresh_flow lvl in
  let d1n, d1p = fresh_flow lvl in
  let d2n, d2p = fresh_flow lvl in
  let r1n, r1p = fresh_flow lvl in
  let r1'n, _r1'p = fresh_flow lvl in
  let r2n, r2p = fresh_flow lvl in
  subtype env r1p r1'n |> ok;
  subtype env (tcons (func [d1n] r1p)) fn |> ok;
  subtype env (tcons (func [d2n] r2p)) fn |> ok;
  let ty = (tcons (func [r1n;r2n] (tcons (tuple [fp;d1p;d2p])))) in
  dump env ty


let match_bug () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  subtype env ap bn |> ok;
  let b1, b2 = match_as_fn env bp in
  let a1, a2 = match_as_fn env ap in
  subtype env a2 (Tcons Cons.bottom) |> ok;
  dump env (tcons (func [a1; b1; an] (tcons (tuple [a2; b2; bp]))))
  

let chain () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let a = Array.init 10 (fun _ -> fresh_flow lvl) in
  let n = Array.map fst a and p = Array.map snd a in
  subtype env p.(5) (tcons Int) |> ok;
  subtype env p.(4) n.(5) |> ok;
  subtype env p.(3) n.(4) |> ok;
  subtype env p.(8) n.(9) |> ok;
  subtype env p.(5) n.(6) |> ok;
  subtype env p.(0) n.(1) |> ok;
  subtype env p.(3) (Ttop None) |> ok;
  subtype env p.(2) n.(3) |> ok;
  subtype env p.(1) n.(2) |> ok;
  subtype env p.(7) n.(8) |> ok;
  subtype env p.(6) n.(7) |> ok;
  dump env (tcons (func [n.(0)] p.(9)))

let dirbug () =
  next_flexvar_id := 0;
  let env = Env_nil and lvl = Env_level.initial in
  let an, _ap = fresh_flow lvl in
  let _bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  let dn, dp = fresh_flow lvl in
  subtype env (tcons (func [an] bp)) (tcons (func [cp] dn)) |> ok;
  dump env (tcons (tuple [tcons (func [an] bp); tcons (func [cn] dp)]))

let poly () =
  next_flexvar_id := 0;
  let env = Env_nil and _lvl = Env_level.initial in
  let bvar ?(index=0) ?(rest) var =
    match rest with
    | None -> Tvar (Vbound {index; var; loc=None})
    | Some rest -> Tjoin (rest, Tvar(Vbound{index; var; loc=None})) in
  let t1 () =
    Tpoly {vars = IArray.of_array [| ("A",noloc), None; ("B",noloc), None |];
           body= tcons (func
                   [bvar 0]
                   (tcons (func
                     [bvar 1]
                     (bvar 1 ~rest:(bvar 0))))) } in
  let t2 () =
    Tpoly {vars = IArray.of_array [| ("X",noloc), None |];
           body = tcons (func [bvar 0] (tcons (func [bvar 0] (bvar 0))))} in
  let t3 () =
    Tpoly {vars = IArray.of_array [| ("P",noloc), None |];
           body = tcons (func [bvar 0] (
             Tpoly {vars=IArray.of_array [| ("Q",noloc), None |];
                    body = tcons (func [bvar 0] (bvar ~rest:(bvar ~index:1 0) 0))}))} in
  print_endline "t1 = t2";
  subtype env (t1 ()) (t2 ()) |> ok;
  subtype env (t2 ()) (t1 ()) |> ok;
  print_endline "t3 <= t1, t2";
  subtype env (t3 ()) (t2 ()) |> ok;
  subtype env (t3 ()) (t1 ()) |> ok;
  let sub = 
    match subtype env (t1 ()) (t3 ()) with
    | Ok () -> true
    | Error _ -> false in
  Printf.printf "t1 <= t3: %b\n" sub;
(*  subtype env (t2 ()) (t3 ()) |> ok;*)
  ()

let flexself () =
  let env = Env_nil and lvl = Env_level.initial in

  (* UBvar optimisation *)
  next_flexvar_id := 0;
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  subtype env ap bn |> ok;
  subtype env bp cn |> ok;
  subtype env ap cn |> ok;
  dump env (tcons (func [an] cp));

  (* Attempted UBvar recursion (should become UBcons) *)
  next_flexvar_id := 0;
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  subtype env ap bn |> ok;
  subtype env bp cn |> ok;
  subtype env cp an |> ok;
  dump env ap;

  (* UBcons recursion, multiple steps to fixed point *)
  next_flexvar_id := 0;
  let an, ap = fresh_flow lvl in
  let bn, bp = fresh_flow lvl in
  let cn, cp = fresh_flow lvl in
  subtype env (tcons Int) cn |> ok;
  subtype env bp an |> ok;
  subtype env cp an |> ok;
  subtype env ap bn |> ok;
  dump env ap

let () = choosy ()
let () = lbs ()
let () = match_bug ()
let () = chain ()
let () = dirbug ()
let () = poly ()
let () = flexself ()
