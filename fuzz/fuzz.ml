open Crowbar
open Lang
open Lang.Exp

let mkident s : ident = { label = s; shift = 0}, noloc

let mkty t = (Some t, noloc)
let mkexp e = (Some e, noloc)

let fields gen =
    let dots = function true -> [Tuple_fields.Fdots] | false -> [] in
    choose [
      (map [gen; bool] @@ fun a d -> Tuple_fields.(collect_fields (Fnamed ("foo", a) :: dots d)));
      (map [gen; gen; bool] @@ fun a b d -> Tuple_fields.(collect_fields (Fnamed ("foo", a) :: Fnamed ("bar", b) :: dots d)));
      (map [gen; bool] @@ fun a d -> Tuple_fields.(collect_fields (Fnamed ("bar", a) :: dots d)));
      map [gen; gen; bool] @@ fun a b d -> Tuple_fields.(collect_fields (Fpos a :: Fpos b :: dots d))]
  

let tyexp = fix @@ fun tyexp ->
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
    map [fields tyexp; tyexp] (fun a b -> Tfunc (a, b));
    map [fields tyexp] (fun a -> Trecord a);

    map [list bound; tyexp] (fun a b -> Tforall (a, b))
  ] in
  map [tyexp'] mkty

let tyexp = with_printer Typedefs.pp_tyexp tyexp

let typolybounds =
  list1 @@ map [choose [const "A";const "B";const "C";const "D"]; option tyexp] @@ fun s t -> ((s,Exp.noloc), t)

let tyexp' =
  map [typolybounds; tyexp] (fun a b -> mkty (Tforall (a, b)))

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
  

(*
let () =
  add_test ~name:"refl" [tyexp'] refl

let () =
  add_test ~name:"compare" [tyexp; tyexp] compare

let () =
  add_test ~name:"commute" [option tyexp;option tyexp;option tyexp;option tyexp;tyexp;tyexp;tyexp;tyexp] commute

let () =
  add_test ~name:"trans" [tyexp'; tyexp'; tyexp'] transitive
*)

let pat = fix @@ fun pat ->
  let pat' = choose [
    const (Pvar ("a",noloc));
    const (Pvar ("b",noloc));
    const (Pvar ("c",noloc));
    map [fields pat] (fun f -> Ptuple f)
  ] in
  map [pat'] mkexp

let exp = fix @@ fun exp ->
  let exp' = choose [
    const (Lit (Int 1, noloc));
    const (Lit (Bool true, noloc));
    const (Var (mkident "a"));
    const (Var (mkident "b"));
    const (Var (mkident "c"));
    map [option typolybounds;
         fields (pair pat (option tyexp'));
         option tyexp;
         exp]
      (fun poly p t e -> Fn (poly,p,t,e));
    map [exp; fields exp] (fun f e -> App (f, e));
    map [fields exp] (fun t -> Tuple t);
    map [pat; option tyexp; exp; exp] (fun p t e b -> Let (p, t, e, b));
    map [exp; choose [const "foo"; const "bar"]] (fun e s -> Proj (e, (s,noloc)));
    map [exp; exp; exp] (fun e1 e2 e3 -> If (e1,e2,e3));
    map [exp; tyexp] (fun e t -> Typed (e, t));
  ] in
  map [exp'] mkexp

let exp = with_printer Typedefs.pp_exp exp

let typeable_exp =
  map [exp] @@ fun e ->
    match Check.elab_gen Env_nil None (fun env -> Check.infer env e) with
    | t, elab ->
       let poly, _ty, elab = Elab.elaborate Env_nil elab in
       (* weak poly *)
       if poly <> None then bad_test ();
       e, elab, t
    | exception (Failure _ | Typedefs.Unimplemented _) -> bad_test ()

let typeable_exp =
  with_printer (fun ppf (e,elab,t) -> Format.fprintf ppf "%a@ %a@ %a" Typedefs.pp_exp e Typedefs.pp_exp elab Typedefs.pp_ptyp t) typeable_exp

let retype (e, elab, t) =
  let te = Typedefs.unparse_ptyp ~flexvar:ignore t in
  let t' = Check.typ_of_tyexp Env_nil te in
  let _ = Check.check Env_nil e t' in
  let _ = Check.check Env_nil elab t' in
  ()

let () =
  add_test ~name:"retype" [typeable_exp] retype
