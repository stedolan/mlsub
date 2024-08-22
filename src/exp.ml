open Location

type 'a mayloc = 'a option loc

type literal = Int of int | String of string | Bool of bool
type symbol = string loc
type ident = ident' loc and ident' =
  { label : string; shift : int }

type tuple_tag =
  | Anon_tag
  | Struct_tag of string loc
  | Named_tag of symbol

(* Expressions *)

(* FIXME: move somewhere new? *)
type mand_flag =
  | Mandatory
  | Optional

type extensible_flag =
  | Ext_open
  | Ext_closed

type 'a fields =
  | Ftuple of 'a list * extensible_flag
  | Frecord of (Tuple_fields.field_name loc * mand_flag * 'a option) list * extensible_flag

let empty_fields = Ftuple ([], Ext_closed)

let map_fields ?(loc=Fun.id) f = function
  | Ftuple (x,ext) -> Ftuple (List.mapi (fun i x -> f (Tuple_fields.Field_positional i, Mandatory) x) x, ext)
  | Frecord (fs,ext) -> Frecord (List.map (fun ((s,sloc),m,x) -> (s,loc sloc), m, Option.map (f (s,m)) x) fs, ext)

(* FIXME: is this a better repr? *)
let record_fields ~loc = function
  | Ftuple (xs, ext) ->
     List.mapi (fun i x -> (Tuple_fields.Field_positional i, loc), Mandatory, Some x) xs, ext
  | Frecord (fields, ext) -> fields, ext

let of_record_fields ~fopen fs =
  match
    List.mapi (fun i x ->
      match x with
      | (Tuple_fields.Field_positional j, _), Mandatory, Some x when i = j -> x
      | _ -> raise_notrace Exit) fs
  with
  | ts -> Ftuple (ts, fopen)
  | exception Exit -> Frecord (fs, fopen)

type exp = exp' mayloc and exp' =
  (* 42 or "hello" *)
  | Lit of literal loc
  (* x *)
  | Var of ident
  (* fn [...](a, b, c) { ... } *)
  | Fn of func_def
  (* fn f(a, b, c) { .... }; ... *)
  | FnDef of symbol * func_def * exp
  (* f(...) *)
  | App of exp * (string option * exp) list
  (* (a, b, c) or {x: a, y, z: c}*)
  | Tuple of tuple_tag option * exp fields
  (* let a : t = ...; ... *)
  | Let of pat * tyexp option * exp * exp
  (* e; e *)
  | Seq of exp * exp
  (* a.foo *)
  | Proj of exp * symbol
  (* if a { foo } else { bar } *)
  | If of exp * exp * exp
  (* match e { p => e | ... } *)
  | Match of exp list loc * case list
  (* (e : A) *)
  | Typed of exp * tyexp
  (* @foo *)
  | Pragma of string

and case = pat list list loc * exp

and func_def = typolybounds option * parameters * tyexp option * exp

and parameters = (pat * tyexp option) list

(* Patterns *)

and pat = pat' mayloc and pat' =
  | Pany
  | Pbind of symbol * pat
  | Ptuple of tuple_tag option * pat fields
  | Por of pat * pat

(* Type expressions *)

and tyexp = tyexp' mayloc and tyexp' =
  | Tforall of typolybounds * tyexp
  | Ttyvar of symbol
  | Trecord of tuple_tag option * tyarg list * tyexp fields
  | Tfunc of tyexp list * tyexp
  | Tjoin of tyexp * tyexp

and tyarg = tyarg' mayloc and tyarg' =
  | Arg_pos of tyexp
  | Arg_neg of tyexp
  | Arg_gen of tyexp
  | Arg_both of {neg:tyexp; pos:tyexp}

and typolybounds =
  (symbol * tyexp option) list

type variance_spec =
  { occurs_pos: [`No | `Strict | `Yes];
    occurs_neg: [`No | `Yes] }

type type_decl_body =
  | Dty_record of tyexp fields loc
  | Dty_variant of (symbol * tyexp fields loc) list

type decl = decl' mayloc and decl' =
  | Dfn of symbol * func_def
  | Dtype of symbol * (variance_spec option * symbol) list * type_decl_body

type mapper = {
  loc : mapper -> location -> location;
  exp : mapper -> exp -> exp;
  pat : mapper -> pat -> pat;
  tyexp : mapper -> tyexp -> tyexp;
  decl : mapper -> decl -> decl;
}
let map_exp m e = m.exp m e
let map_tyexp m t = m.tyexp m t
let map_prog m p = List.map (m.decl m) p

let mapper =
  let loc _ l = l in

  let sym r (s, sloc) = s, r.loc r sloc in

  let mayloc f recr = function
    | (None, l) -> (None, recr.loc recr l)
    | (Some x, l) -> (Some (f recr x), recr.loc recr l) in

  let fndef r (poly, args, ret, body) =
    let poly = Option.map (List.map (fun (s, t) -> (sym r s, Option.map (r.tyexp r) t))) poly in
    let args = List.map (fun (p, t) -> (r.pat r p, Option.map (r.tyexp r) t)) args in
    let ret = Option.map (r.tyexp r) ret in
    let body = r.exp r body in
    (poly, args, ret, body)
  in

  let case r ((pats, ploc), exp) = ((List.map (List.map (r.pat r)) pats, r.loc r ploc), r.exp r exp) in

  let fields f r fs = map_fields ~loc:(r.loc r) (fun _fn e -> f r e) fs in

  let tuple_tag r t = match t with
    | Anon_tag -> Anon_tag
    | Struct_tag t -> Struct_tag (sym r t)
    | Named_tag t -> Named_tag (sym r t)
  in

  let exp = mayloc @@ fun r e -> match e with
    | Lit (l, loc) ->
       Lit (l, r.loc r loc)
    | Var (n, loc) ->
       Var (n, r.loc r loc)
    | Fn def ->
       Fn (fndef r def)
    | FnDef (s, def, body) ->
       FnDef (sym r s, fndef r def, r.exp r body)
    | App (f, args) ->
       App (r.exp r f, List.map (fun (k, x) -> k, r.exp r x) args)
    | Tuple (tag, es) ->
       Tuple (Option.map (tuple_tag r) tag, fields r.exp r es)
    | Let (p, ty, e, body) ->
       Let (r.pat r p, Option.map (r.tyexp r) ty, r.exp r e, r.exp r body)
    | Seq (e1, e2) ->
       Seq (r.exp r e1, r.exp r e2)
    | Proj (e, s) ->
       Proj (r.exp r e, sym r s)
    | If (e, et, ef) ->
       If (r.exp r e, r.exp r et, r.exp r ef)
    | Typed (e, t) ->
       Typed (r.exp r e, r.tyexp r t)
    | Match ((e, eloc), cases) ->
       Match ((List.map (r.exp r) e, r.loc r eloc), List.map (case r) cases)
    | Pragma s ->
       Pragma s
  in

  let pat = mayloc @@ fun r p -> match p with
    | Pany -> Pany
    | Pbind (s, p) -> Pbind (sym r s, r.pat r p)
    | Ptuple (tag, ps) ->
       Ptuple (Option.map (tuple_tag r) tag, fields r.pat r ps)
    | Por (p, q) -> Por (r.pat r p, r.pat r q)
  in

  let tyexp = mayloc @@ fun r t -> match t with
    | Tforall (bounds, body) ->
       let bounds = List.map (fun (s, t) -> (sym r s, Option.map (r.tyexp r) t)) bounds in
       let body = r.tyexp r body in
       Tforall (bounds, body)
    | Ttyvar v ->
       Ttyvar (sym r v)
    | Trecord (tag, args, ts) ->
       let tyarg = mayloc @@ fun r t -> match t with
         | Arg_pos t -> Arg_pos (r.tyexp r t)
         | Arg_neg t -> Arg_neg (r.tyexp r t)
         | Arg_gen t -> Arg_gen (r.tyexp r t)
         | Arg_both {neg;pos} -> Arg_both {neg=r.tyexp r neg; pos=r.tyexp r pos}
       in
       Trecord (Option.map (tuple_tag r) tag,
                List.map (tyarg r) args,
                fields r.tyexp r ts)
    | Tfunc (args, ret) ->
       Tfunc (List.map (r.tyexp r) args, r.tyexp r ret)
    | Tjoin (s, t) ->
       Tjoin (r.tyexp r s, r.tyexp r t)
  in

  let ty_decl_body r = function
    | Dty_record (fs,loc) -> Dty_record (fields r.tyexp r fs, r.loc r loc)
    | Dty_variant vs -> Dty_variant (List.map (fun (s,(fs,loc)) -> sym r s, (fields r.tyexp r fs, r.loc r loc)) vs)
  in

  let decl = mayloc @@ fun r d -> match d with
    | Dfn (s, f) -> Dfn (sym r s, fndef r f)
    | Dtype (s, ps, body) ->
       Dtype (sym r s, List.map (fun (v,s) -> v, sym r s) ps, ty_decl_body r body)
  in
  { loc; exp; pat; tyexp; decl }

let strip_locations =
  { mapper with loc = fun _ _ -> noloc }

let equal e1 e2 = map_exp strip_locations e1 = map_exp strip_locations e2
let equal_tyexp e1 e2 = map_tyexp strip_locations e1 = map_tyexp strip_locations e2

let equal_prog p1 p2 = map_prog strip_locations p1 = map_prog strip_locations p2
