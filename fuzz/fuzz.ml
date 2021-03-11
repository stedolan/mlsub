open Crowbar
open Lang
open Lang.Exp

let mkident s : ident = { label = s; shift = 0}, noloc

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
  map [tyexp'] @@ fun t -> (Some t, noloc)

let refl ts =
  match Lang.Check.typ_of_tyexp Env_nil ts with
  | exception _ -> bad_test ()
  | t ->
     let error e =
       Printexc.get_callstack 1000 |> Printexc.print_raw_backtrace stdout;
       Check.report e in
     Types.subtype ~error Env_nil t t

let () =
  add_test ~name:"refl" [with_printer Typedefs.pp_tyexp tyexp] refl
