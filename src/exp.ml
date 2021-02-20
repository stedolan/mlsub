open Tuple_fields

type location =
  { source : string;
    loc_start : Lexing.position;
    loc_end : Lexing.position }

let noloc =
  let loc : Lexing.position = {pos_fname="_";pos_lnum=0;pos_cnum=0;pos_bol=0} in
  { source = "_"; loc_start = loc; loc_end = loc}

type 'a loc = 'a * location

type 'a mayloc = 'a option loc

type literal = Int of int | String of string | Bool of bool
type symbol = string loc
type ident = ident' loc and ident' =
  { label : string; shift : int }

(* Expressions *)

type exp = exp' mayloc and exp' =
  (* 42 or "hello" *)
  | Lit of literal loc
  (* x *)
  | Var of ident
  (* fn [...](a, b, c) { ... } *)
  | Fn of typolybounds option * parameters * tyexp option * exp
  (* fn f(a, b, c) { .... }; ... *)
  (* | Def of symbol * typed_pats * exp * exp *)
  (* f(...) *)
  | App of exp * exp tuple_fields
  (* (a, b, c) or {x: a, y, z: c}*)
  | Tuple of exp tuple_fields
  (* let a : t = ...; ... *)
  | Let of pat * tyexp option * exp * exp
  (* a.foo *)
  | Proj of exp * symbol
  (* if a { foo } else { bar } *)
  | If of exp * exp * exp
  (* (e : A) *)
  | Typed of exp * tyexp
  (* (e) *)
  | Parens of exp
  (* @foo *)
  | Pragma of string

and parameters = (pat * tyexp option) tuple_fields

(* Patterns *)

and pat = pat' mayloc and pat' =
  | Ptuple of pat tuple_fields
  | Pvar of symbol
  | Pparens of pat

(* Type expressions *)

and tyexp = tyexp' mayloc and tyexp' =
  | Tnamed of ident
  | Tforall of typolybounds * tyexp
  | Trecord of tyexp tuple_fields
  | Tfunc of tyexp tuple_fields * tyexp
  | Tparen of tyexp
  | Tjoin of tyexp * tyexp

and typolybounds =
  (symbol * tyexp option) list


module Strip_locations = struct
  let rec exp (e, _) = Option.map exp' e, noloc
  and exp' = function
    | Lit (l, _) -> Lit (l, noloc)
    | Var (id, _) -> Var (id, noloc)
    | Fn (poly, args, ret, body) ->
       Fn(Option.map typolybounds poly,
          map_fields (fun _ (p, ty) -> (pat p, Option.map tyexp ty)) args,
          Option.map tyexp ret,
          exp body)
    | App (e, args) ->
       App (exp e, map_fields (fun _ e -> exp e) args)
    | Tuple es ->
       Tuple (map_fields (fun _ e -> exp e) es)
    | Let (p, ty, e, body) ->
       Let (pat p, Option.map tyexp ty, exp e, exp body)
    | Proj (e, (s,_)) ->
       Proj (exp e, (s,noloc))
    | If (e, t, f) ->
       If (exp e, exp t, exp f)
    | Typed (e, ty) ->
       Typed (exp e, tyexp ty)
    | Parens e ->
       Parens (exp e)
    | Pragma s -> Pragma s
  and pat (p, _) = Option.map pat' p, noloc
  and pat' = function
    | Ptuple ps -> Ptuple (map_fields (fun _ p -> pat p) ps)
    | Pvar (s, _) -> Pvar (s, noloc)
    | Pparens p -> Pparens (pat p)
  and tyexp (t, _) = Option.map tyexp' t, noloc
  and tyexp' = function
    | Tnamed (s, _) -> Tnamed (s, noloc)
    | Tforall (poly, t) -> Tforall (typolybounds poly, tyexp t)
    | Trecord ts -> Trecord (map_fields (fun _ ty -> tyexp ty) ts)
    | Tfunc (args, ret) -> Tfunc (map_fields (fun _ ty -> tyexp ty) args, tyexp ret)
    | Tparen t -> Tparen (tyexp t)
    | Tjoin (a, b) -> Tjoin (tyexp a, tyexp b)
  and typolybounds (bounds : typolybounds) =
    bounds |> List.map (fun ((s,_), b) ->
      ((s,noloc), Option.map tyexp b))
end

let equal e1 e2 = Strip_locations.(exp e1 = exp e2)
