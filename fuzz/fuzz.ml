open Crowbar
open Lang
open Lang.Exp

let mkident s : ident = { label = s; shift = 0}, noloc

let mkty t = (Some t, noloc)

let tyexp = fix @@ fun tyexp ->
  let tfields =
    (* FIXME extend *)
    let dots = function true -> [Tuple_fields.Fdots] | false -> [] in
    choose [
      (map [tyexp; bool] @@ fun a d -> Tuple_fields.(collect_fields (Fnamed ("foo", a) :: dots d)));
      (map [tyexp; tyexp; bool] @@ fun a b d -> Tuple_fields.(collect_fields (Fnamed ("foo", a) :: Fnamed ("bar", b) :: dots d)));
      (map [tyexp; bool] @@ fun a d -> Tuple_fields.(collect_fields (Fnamed ("bar", a) :: dots d)));
      map [tyexp; tyexp; bool] @@ fun a b d -> Tuple_fields.(collect_fields (Fpos a :: Fpos b :: dots d))] in
  let bound =
    map [choose [const "A";const "B";const "C";const "D"]; option tyexp] @@ fun s t -> ((s,Exp.noloc), t) in
  let tyexp' = choose [
    const (Tnamed (mkident "int"));
    const (Tnamed (mkident "bool"));
    const (Tnamed (mkident "nothing"));
    const (Tnamed (mkident "any"));

    const (Tnamed (mkident "A"));
    const (Tnamed (mkident "B"));
    const (Tnamed (mkident "C"));
    const (Tnamed (mkident "D"));

    map [tyexp; tyexp] (fun a b -> Tjoin (a, b));
    map [tfields; tyexp] (fun a b -> Tfunc (a, b));
    map [tfields] (fun a -> Trecord a);

    map [list bound; tyexp] (fun a b -> Tforall (a, b))
  ] in
  map [tyexp'] mkty

let tyexp = with_printer Typedefs.pp_tyexp tyexp

let tyexp' =
  let bound =
    map [choose [const "A";const "B";const "C";const "D"]; option tyexp] @@ fun s t -> ((s,Exp.noloc), t) in
  map [list1 bound; tyexp] (fun a b -> mkty (Tforall (a, b)))

let tyexp' = with_printer Typedefs.pp_tyexp tyexp'

let refl ts =
  match Lang.Check.typ_of_tyexp Env_nil ts with
  | exception _ -> bad_test ()
  | t ->
     let error e =
       Printexc.get_callstack 1000 |> Printexc.print_raw_backtrace stdout;
       Check.report e in
     Types.subtype ~error Env_nil t t

let compare a b =
  match Lang.Check.typ_of_tyexp Env_nil a, Lang.Check.typ_of_tyexp Env_nil b with
  | exception _ -> bad_test ()
  | a, b ->
     try Types.subtype ~error:(fun _ -> raise Exit) Env_nil a b
     with Exit -> ()

let parse t = Lang.Check.typ_of_tyexp Env_nil t

let commute a b c d p q r s =
  let pair x y = mkty (Trecord (Tuple_fields.(collect_fields [Fpos x; Fpos y]))) in
  let lbound = [("A", noloc), a; ("B",noloc), b] in
  let rbound = [("C", noloc), c; ("D",noloc), d] in
  let tl = mkty (Tforall (lbound, pair p q)) in
  let tr = mkty (Tforall (rbound, pair r s)) in

  let tl, tr = try parse tl, parse tr with _ -> bad_test () in
  let tl' = mkty (Tforall (lbound, pair q p)) in
  let tr' = mkty (Tforall (rbound, pair s r)) in
  let tl', tr' = parse tl', parse tr' in

  let subt a b =
    match Types.subtype ~error:(fun _ -> raise Exit) Env_nil a b with
    | () -> `Yes
    | exception Exit -> `No in
  assert (subt tl tr = subt tl' tr')

let transitive a b c =
  let a, b, c = try parse a, parse b, parse c with _ -> bad_test () in
  let subt a b =
    match Types.subtype ~error:(fun _ -> raise Exit) Env_nil a b with
    | () -> true
    | exception Exit -> false in
  let ab = subt a b and bc = subt b c and ca = subt c a in
  let ba = subt b a and cb = subt c b and ac = subt a c in
  assert ((ab && bc) <= ac);
  assert ((bc && ca) <= ba);
  assert ((ca && ab) <= cb);
  assert ((cb && ba) <= ca);
  assert ((ac && cb) <= ab);
  assert ((ba && ac) <= bc)
  


let () =
  add_test ~name:"refl" [tyexp'] refl

(*
let () =
  add_test ~name:"compare" [tyexp; tyexp] compare

let () =
  add_test ~name:"commute" [option tyexp;option tyexp;option tyexp;option tyexp;tyexp;tyexp;tyexp;tyexp] commute
*)

(*
let () =
  add_test ~name:"trans" [tyexp'; tyexp'; tyexp'] transitive
*)
