(*
 * Core definitions used by the typechecker
 *)

module IntMap = Map.Make (struct type t = int let compare = compare end)
module StrMap = Map.Make (struct type t = string let compare = compare end)

(* Later, maybe intern these? *)
type symbol = string
module SymMap = Map.Make (struct type t = symbol let compare = compare end)

type polarity = Pos | Neg

(* Head type constructors. These do not bind type variables.
   FIXME: might be good to preserve field order *)
type 'a cons_head =
  | Top
  | Bot
  | Record of 'a cons_head_fields
  | Func of 'a cons_head_fields * 'a

and 'a cons_head_fields =
  (* Positional elements are encoded as field names "0", "1", etc. *)
  (* FIXME: maybe preserve field order here? *)
  'a StrMap.t

type var_sort = Flexible | Rigid
let () = assert (Flexible < Rigid) (* required for vset ordering *)

(* Typing environment *)
type env =
  | Env_empty
  | Env_cons of {
      entry : env_entry;
      level : int;
      rest : env;
      (* Flexible variables, being inferred *)
      (* Their scope includes the current entry *)
      mutable tyvars : flexvar Vector.t;
    }

(* Entries in the typing environment *)
and env_entry =
  (* Binding x : τ *)
  | Eval of symbol * typ
  (* Marker for scope of generalisation (let binding) *)
  | Egen
  (* Rigid type variables (abstract types, checked forall) *)
  | Erigid of {
      (* all fields immutable, despite array/table *)
      (* FIXME: explain why predicativity matters here *)
      vars : rigvar array;
      flow : rig_flow;
    }

(* Flow relation between rigid variables of the same binding group *)
and rig_flow = (int * int, unit) Hashtbl.t

(* Simple types (the result of inference)
   Each styp contains no bound type variables *)
and styp =
  { tyvars: vset; cons: styp cons_head; pol: polarity }

(* Sets of type variables.
   Entries are ordered by environment (longest env first),
   with flexible variables before rigid at the same env *)
and vset =
  | VSnil
  | VScons of {
      env : env;
      sort : var_sort;
      vars : int list; (* sorted *)
      rest : vset
    }

(* Flexible type variables.
   Maintain the ε-invariant:
   for flexible variables α, β from the same binding group,
   β ∈ α.pos.tyvars iff α ∈ β.neg.tyvars *)
and flexvar = {
    (* positive component, lower bound *)
    mutable pos : styp;
    (* negative component, upper bound *)
    mutable neg : styp;
  }

(* Rigid type variables *)
and rigvar = {
  (* lower bound / negative component *)
  rig_lower : styp;
  (* upper bound / positive component *)
  rig_upper : styp;
}

(* An styp, possibly containing bound variables *)
and styp_bound =
  | Tstyp_bound of {
      tyvars : vset;
      cons: styp_bound cons_head;
      bvars: boundref list; (* in *descending* order by de Bruijn index *)
      pol: polarity;
    }
  (* A Tstyp_simple contains no bound variables *)
  | Tstyp_simple of styp

(* Reference to a bound variable *)
and boundref = {
  b_group_idx : int; (* de Bruijn index of binder group *)
  b_sort : var_sort;
  b_vars : int list;  (* IDs within binder group *)
}

(* General polymorphic types.  Inference may produce these after
   generalisation, but never instantiates a variable with one.
   Inference never produces Poly_neg *)
and typ =
  | Tsimple of styp_bound
  | Tcons of typ cons_head
  (* Forall in a positive position. *)
  | Tpoly_pos of (styp_bound * styp_bound) array * typ
  (* Forall in a negative position *)
  | Tpoly_neg of (styp_bound * styp_bound) array * rig_flow * typ



let polneg = function Pos -> Neg | Neg -> Pos

(* Underconstrained. Might be anything. Identity of meet/join. *)
let ident = function
  | Pos -> Bot
  | Neg -> Top

(* Overconstrained. Must be everything. Annihilator of meet/join. *)
let annih = function
  | Pos -> Top
  | Neg -> Bot

(*
 * Environment ordering and vset merging
 *)

(* Check that one environment is an extension of another *)
let rec assert_env_prefix env ext =
  if env != ext then
    match env, ext with
    | Env_empty, _ -> ()
    | Env_cons _, Env_empty -> assert false
    | Env_cons _, Env_cons { rest; _ } ->
       assert_env_prefix env rest

(* Only defined if one environment is an extension of the other *)
let env_max e1 e2 =
  match e1, e2 with
  | Env_empty, e | e, Env_empty -> e
  | Env_cons { level = l1; _ }, Env_cons { level = l2; _ } ->
     if l1 = l2 then
       (assert (e1 == e2); e1)
     else if l1 < l2 then
       (assert_env_prefix e1 e2; e2)
     else
       (assert_env_prefix e2 e1; e1)

let env_level = function
  | Env_empty -> 0
  | Env_cons { level; _ } -> level

let env_equal env ext =
  assert_env_prefix env ext;
  (env_level env = env_level ext)

let env_cons env entry =
  Env_cons { entry; level = env_level env + 1;
             rest = env; tyvars = Vector.create () }

let env_flexvar env i =
  match env with
  | Env_empty -> assert false
  | Env_cons { tyvars; _ } -> Vector.get tyvars i

let env_rigid_flow env i j =
  match env with
  | Env_cons { entry = Erigid { flow; vars }; _ } ->
     assert (0 <= i && i < Array.length vars);
     assert (0 <= j && j < Array.length vars);
     Hashtbl.mem flow (i, j)
  | _ ->
     failwith "error: no rigid vars here"

let rec int_list_union (xs : int list) (ys : int list) =
  match xs, ys with
  | [], rs | rs, [] -> rs
  | x :: xs', y :: ys' when x = y ->
     x :: int_list_union xs' ys'
  | x :: xs', y :: ys' ->
     if x < y then
       x :: int_list_union xs' ys
     else
       y :: int_list_union xs ys'

let rec vset_union vars1 vars2 =
  match vars1, vars2 with
  | VSnil, v | v, VSnil -> v
  | VScons v1, VScons v2 when
     v1.env == v2.env && v1.sort = v2.sort ->
     VScons {
       env = v1.env;
       sort = v1.sort;
       vars = int_list_union v1.vars v2.vars;
       rest = vset_union v1.rest v2.rest
     }
  | VScons v1, VScons v2 ->
     let l1 = env_level v1.env and l2 = env_level v2.env in
     if l1 > l2 || (l1 = l2 && v1.sort < v2.sort) then
       VScons { v1 with rest = vset_union v1.rest vars2 }
     else
       VScons { v2 with rest = vset_union vars1 v2.rest }

let rec vset_lookup venv vsort = function
  | VSnil -> []
  | VScons { env; sort; vars; _ }
       when env == venv && sort = vsort ->
     vars
  | VScons { env; rest; _ } ->
     if env_level env < env_level venv then []
     else vset_lookup venv vsort rest


let styp_uncons venv vsort ({ tyvars; cons; pol } as t) =
  match tyvars with
  | VSnil -> t, []
  | VScons { env; sort; vars; rest }
    when env == venv && sort = vsort ->
     { tyvars = rest; cons; pol }, vars
  | VScons { env; sort; _ } ->
     assert_env_prefix env venv;
     assert (env_level env < env_level venv
             || (sort = Rigid && vsort = Flexible));
     t, []



(*
 * Opening/closing of binders
 *)


(* FIXME: might need to be polarity-aware *)
let map_head pol f = function
  | Top -> Top
  | Bot -> Bot
  | Record fields ->
     Record (StrMap.map (f pol) fields)
  | Func (args, res) ->
     Func (StrMap.map (f (polneg pol)) args, f pol res)

let cons_styp pol (tyvars : vset) (cons : styp cons_head) =
  { pol; tyvars; cons }

let cons_styp_bound pol (tyvars : vset) bvars (t : styp_bound cons_head) =
  match bvars with
  | _ :: _ -> Tstyp_bound { tyvars; cons = t; pol; bvars }
  | [] ->
    match map_head pol (fun _pol s ->
              match s with
                Tstyp_simple s -> s
              | Tstyp_bound _ -> raise_notrace Exit) t with
    | exception Exit ->
       Tstyp_bound { tyvars; cons = t; pol; bvars = [] }
    | cons ->
       Tstyp_simple { tyvars; cons; pol }

let cons_typ pol cons =
  match map_head pol (fun _pol s ->
            match s with Tsimple s -> s | _ -> raise_notrace Exit) cons with
  | exception Exit ->
     Tcons cons
  | cons -> Tsimple (cons_styp_bound pol VSnil [] cons)

let rec open_styp sort vars ix pol' = function
  | Tstyp_simple _ as s -> s  (* No bound vars, so nothing to open  *)
  | Tstyp_bound { tyvars; cons; bvars; pol } ->
     assert (pol = pol');
     let cons = map_head pol (open_styp sort vars ix) cons in
     (* We're opening the outermost binder,
        so if it appears it must be at the head of bvars *)
     begin match bvars with
     | { b_group_idx; b_sort; b_vars } :: bs
          when b_group_idx = ix ->
        (* While there can be variables of different sorts attached
           to the same environment, there can only be one sort of
           variable bound by a given binder *)
        assert (b_sort = sort);
        let tyvars =
          List.fold_left (fun vs i -> vset_union vs vars.(i))
            VSnil b_vars in
        cons_styp_bound pol tyvars bs cons
     | bvars ->
        cons_styp_bound pol tyvars bvars cons
     end     

let rec open_typ sort vars ix pol = function
  | Tsimple s -> Tsimple (open_styp sort vars ix pol s)
  | Tcons cons ->
     cons_typ pol (map_head pol (open_typ sort vars ix) cons)
  | Tpoly_pos (bounds, body) ->
     assert (pol = Pos);
     let ix = ix + 1 in
     Tpoly_pos (Array.map (fun (l,u) ->
                    open_styp sort vars ix pol l,
                    open_styp sort vars ix (polneg pol) u) bounds,
                open_typ sort vars ix pol body)
  | Tpoly_neg (bounds, flow, body) ->
     assert (pol = Neg);
     let ix = ix + 1 in
     Tpoly_neg (Array.map (fun (l, u) ->
                    open_styp sort vars ix pol l,
                    open_styp sort vars ix (polneg pol) u) bounds,
                flow,
                open_typ sort vars ix pol body)

let is_styp = function
  | Tstyp_simple s -> s
  | Tstyp_bound _ -> failwith "type scoping error"

(* Open a ∀⁺ binder, creating flexible variables *)
let enter_poly_pos env vars =
  let env = env_cons env Egen in
  let tyvars = match env with Env_cons { tyvars; _ } -> tyvars | _ -> assert false in (* uglllyyyy. *)
  let nvars = Array.length vars in
  for _i = 0 to nvars - 1 do
    Vector.push tyvars { pos = cons_styp Pos VSnil Bot;
                         neg = cons_styp Neg VSnil Top }
  done;
  let vsets = Array.init nvars (fun i ->
    VScons { env; sort = Flexible; vars = [i]; rest = VSnil }) in
  for i = 0 to nvars - 1 do
    let v = Vector.get tyvars i in
    let (pos, neg) = vars.(i) in
    v.pos <- is_styp (open_styp Flexible vsets 0 Pos pos);
    v.neg <- is_styp (open_styp Flexible vsets 0 Neg neg);
  done;
  env, vsets

(* Open a ∀⁻ binder, creating rigid variables *)
let enter_poly_neg env bounds flow =
  let nvars = Array.length bounds in
  let vars = Array.init nvars (fun _ ->
    { rig_lower = cons_styp Neg VSnil Bot;
      rig_upper = cons_styp Pos VSnil Top }) in
  let env_entry = Erigid { vars; flow } in
  let env = env_cons env env_entry in
  let vsets = Array.init nvars (fun i ->
    VScons { env; sort = Rigid; vars = [i]; rest = VSnil }) in
  for i = 0 to nvars - 1 do
    let (lower, upper) = bounds.(i) in
    vars.(i) <-
      { rig_lower = is_styp (open_styp Rigid vsets 0 Neg lower);
        rig_upper = is_styp (open_styp Rigid vsets 0 Pos upper) }
  done;
  env, vsets


(*
 * Well-formedness checks.
 * The wf_foo functions check for local closure also.
 *)

let rec wf_cons pol env wf = function
  | Bot | Top -> ()
  | Record fields ->
     wf_cons_fields pol env wf fields
  | Func (args, res) ->
     wf_cons_fields (polneg pol) env wf args;
     wf pol env res
and wf_cons_fields pol env wf =
  StrMap.iter (fun _ t -> wf pol env t)

let rec wf_env = function
  | Env_empty -> ()
  | Env_cons { entry; level; rest; tyvars } as env ->
     assert (level = env_level rest + 1);
     wf_env_entry env entry;
     wf_flexvars env tyvars;
     wf_env rest

and wf_flexvars env vars =
  Vector.iteri vars (fun i { pos; neg } ->
    wf_styp Pos env pos;
    wf_styp Neg env neg;
    (* Check the ε-invariant *)
    vset_lookup env Flexible pos.tyvars |> List.iter (fun j ->
      assert (List.mem i (vset_lookup env Flexible
          (Vector.get vars j).neg.tyvars)));
    vset_lookup env Flexible neg.tyvars |> List.iter (fun j ->
      assert (List.mem i (vset_lookup env Flexible
          (Vector.get vars j).pos.tyvars))))
  

and wf_env_entry env = function
  | Eval (_, typ) -> wf_typ Pos env typ
  | Egen -> ()
  | Erigid { vars; flow } ->
     flow |> Hashtbl.iter (fun (i,j) () ->
       assert (i <> j);         (* FIXME: unconvinced by this! *)
       assert (0 <= i && i < Array.length vars);
       assert (0 <= j && j < Array.length vars));
     vars |> Array.iter (fun { rig_lower; rig_upper } ->
       wf_styp Neg env rig_lower;
       wf_styp Pos env rig_upper)

and wf_styp pol' env { tyvars; cons; pol } =
  assert (pol = pol');
  wf_cons pol env wf_styp cons;
  wf_vset pol env tyvars

and wf_typ pol env = function
  | Tcons cons ->
     wf_cons pol env wf_typ cons
  | Tsimple (Tstyp_simple s) ->
     wf_styp pol env s
  | Tsimple (Tstyp_bound _) ->
     (* should be locally closed *)
     assert false
  | Tpoly_pos (vars, body) ->
     assert (pol = Pos);
     let env, vsets = enter_poly_pos env vars in
     wf_typ Pos env (open_typ Flexible vsets 0 pol body)
  | Tpoly_neg (bounds, flow, body) ->
     assert (pol = Neg);
     let env, vsets = enter_poly_neg env bounds flow in
     wf_typ Neg env (open_typ Rigid vsets 0 pol body)

and wf_vset pol env_ext = function
  | VSnil -> ()
  | VScons { env; sort; vars; rest } ->
     assert_env_prefix env env_ext;
     assert (vars <> []);
     let len, env' =
       match sort, env with
       | Flexible, Env_cons { tyvars; rest; _ } ->
          Vector.length tyvars, rest
       | Rigid, Env_cons { entry = Erigid { vars; _ }; rest; _} ->
          Array.length vars, rest
       | _ -> assert false in
     vars |> List.iter (fun i -> assert (i < len));
     assert (vars = List.sort_uniq compare vars);
     wf_vset pol env' rest


(*
 * Printing of internal representations
 *)

open PPrint
let str = utf8string
let rec pr_cons pol pr t =
  match t with
  | Bot -> str "⊥"
  | Top -> str "⊤"
  | Record fs -> pr_cons_fields pol pr fs
  | Func (args, res) ->
     pr_cons_fields (polneg pol) pr args ^^
       blank 1 ^^ str "→" ^^ blank 1 ^^
         pr pol res
and pr_cons_fields pol pr fs =
  let fields = StrMap.fold (fun k x acc -> (k,x)::acc) fs [] in
  let pr_field (k, v) =
    str k ^^ str ":" ^^ blank 1 ^^ pr pol v in
  parens (group (nest 2 (break 0 ^^ separate_map (comma ^^ break 1)
                                      pr_field fields))) 

let rec pr_vset = function
  | VSnil -> []
  | VScons { env; sort; vars; rest } ->
     List.fold_left (fun acc v ->
       let v = match sort with
         | Flexible -> Printf.sprintf "'%d.%d" (env_level env) v
         | Rigid -> Printf.sprintf "#%d.%d" (env_level env) v in
       str v :: acc) (pr_vset rest) vars

let pr_bvars bv =
  List.fold_left (fun acc { b_group_idx; b_sort; b_vars } ->
    List.fold_left (fun acc v ->
      let v = match b_sort with
        | Flexible -> Printf.sprintf "$%d.%d" b_group_idx v
        | Rigid -> Printf.sprintf "$%d.%d" b_group_idx v in
      str v :: acc) acc b_vars) [] bv

let pr_cons_tyvars pol vars cons_orig cons =
  let join = match pol with Pos -> "⊔" | Neg -> "⊓" in
  let join = blank 1 ^^ str join ^^ blank 1 in
  let pvars = separate_map join (fun v -> v) vars in
  match pol, cons_orig, vars with
  | _, _, [] -> cons
  | Pos, Bot, _
  | Neg, Top, _ -> pvars
  | _, _, _ -> parens cons ^^ join ^^ pvars

let rec pr_styp pol { tyvars; cons; _ } =
  pr_cons_tyvars pol (pr_vset tyvars) cons (pr_cons pol pr_styp cons)

let rec pr_styp_bound pol = function
  | Tstyp_simple s -> pr_styp pol s
  | Tstyp_bound { tyvars; cons; bvars; _ } ->
     pr_cons_tyvars pol
       (pr_vset tyvars @ pr_bvars bvars)
       cons (pr_cons pol pr_styp_bound cons)
     

let rec pr_typ pol = function
  | Tsimple s -> pr_styp_bound pol s
  | Tcons cons ->
     pr_cons_tyvars pol [] cons (pr_cons pol pr_typ cons)
  | Tpoly_pos (bounds, body) ->
     str "∀⁺" ^^ blank 1 ^^
       separate_map (str "," ^^ blank 1) (pr_bound Pos) (Array.to_list bounds) ^^
         str "." ^^ blank 1 ^^ pr_typ pol body
  | Tpoly_neg (bounds, flow, body) ->
     str "∀⁻" ^^ blank 1 ^^
       separate_map (str "," ^^ blank 1) (pr_bound Neg) (Array.to_list bounds) ^^
         (Hashtbl.fold (fun (n,p) () acc ->
             acc ^^ comma ^^ break 1 ^^ str (Printf.sprintf "%d ≤ %d" n p)) flow empty) ^^
         str "." ^^ blank 1 ^^ pr_typ pol body

and pr_bound pol (lower, upper) =
  brackets (pr_styp_bound pol lower ^^
              str "," ^^
            pr_styp_bound (polneg pol) upper)

let func a b = Func (StrMap.singleton "x" a, b)

let bvars pol idx sort vs =
  Tstyp_bound { tyvars = VSnil; cons = ident pol; pol;
                bvars = [{ b_group_idx = idx; b_sort = sort;
                           b_vars = vs }] }

let go () =
  let choose1_pos =
    Tpoly_pos ([| cons_styp_bound Pos VSnil [] Bot, cons_styp_bound Neg VSnil [] Top;
                  cons_styp_bound Pos VSnil [] Bot, cons_styp_bound Neg VSnil [] Top |],
               Tsimple (cons_styp_bound Pos VSnil [] (func
                 (bvars Neg 0 Flexible [0])
                 (cons_styp_bound Pos VSnil [] (func
                   (bvars Neg 0 Flexible [1])
                   (bvars Pos 0 Flexible [0; 1])))))) in
  wf_typ Pos Env_empty choose1_pos;
  PPrint.ToChannel.pretty 1. 80 stdout
    (pr_typ Pos choose1_pos ^^ hardline);

