(*
 * Core definitions used by the typechecker
 *)

module IntMap = Map.Make (struct type t = int let compare = compare end)
module StrMap = Map.Make (struct type t = string let compare = compare end)

(* Later, maybe intern these? *)
type symbol = string
module SymMap = Map.Make (struct type t = symbol let compare = compare end)

type polarity = Pos | Neg

(* Head type constructors.
   FIXME: might be good to preserve field order *)
type 'a cons_head =
  (* Underconstrained. Might be anything. Identity of meet/join.
     (⊤ if Neg, ⊥ if Pos *)
  | Ident
  (* Overconstrained. Must be everything. Annihilator of meet/join.
     (⊥ if Neg, ⊤ if Pos *)
  | Annih
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

(* General polymorphic types.  Inference may produce these after
   generalisation, but never instantiates a variable with one.
   Inference never produces Poly_neg *)
and typ =
  | Tcons of {
      tyvars : vset;
      cons : typ cons_head;
      bvars : boundref list; (* in *descending* order by de Bruijn index *)
      pol : polarity;
    }
  (* A Tsimp can always be expressed by expanding to Tcons, but using
     Tsimp implies that it contains no bound variables or binding
     structure, which means it can be skipped by opening / closing.
     FIXME: is this a good idea? *)
  | Tsimp of styp
  (* Forall in a positive position.
     Bounds should not contain Tpoly.
     FIXME: this is a horrible way to express that constraint *)
  | Tpoly_pos of (typ * typ) array * typ
  (* Forall in a negative position *)
  | Tpoly_neg of (typ * typ) array * rig_flow * typ

(* Reference to a bound variable *)
and boundref = {
  b_group_idx : int; (* de Bruijn index of binder group *)
  b_sort : var_sort;
  b_vars : int list;  (* IDs within binder group *)
}



let polneg = function Pos -> Neg | Neg -> Pos


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

let env_cons env entry =
  Env_cons { entry; level = env_level env + 1;
             rest = env; tyvars = Vector.create () }

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
(*
 * Opening/closing of binders
 *)

(* FIXME: might need to be polarity-aware *)
let map_head f = function
  | Ident -> Ident
  | Annih -> Annih
  | Record fields ->
     Record (StrMap.map f fields)
  | Func (args, res) ->
     Func (StrMap.map f args, f res)

let cons_typ pol (tyvars : vset) (t : typ cons_head) =
  match map_head (function Tsimp s -> s | _ -> raise_notrace Exit) t with
  | exception Exit ->
     Tcons { tyvars; cons = t; bvars = []; pol }
  | cons ->
     (* Entirely simple types *)
     Tsimp { tyvars; cons; pol }

let cons_styp pol (tyvars : vset) (cons : styp cons_head) =
  { pol; tyvars; cons }

let rec open_typ sort vars ix = function
  | Tsimp _ as t ->
     (* There is no binding under a Tsimp, so nothing to open *)
     t
  | Tcons { tyvars; cons; bvars; pol } ->
     let cons = map_head (open_typ sort vars ix) cons in
     (* We're opening the outermost binder,
        so if it appears it must be at the head of bvars *)
     begin match bvars with
     | [] ->
        cons_typ pol tyvars cons
     | { b_group_idx; b_sort; b_vars } :: bs
          when b_group_idx = ix ->
        (* While there can be variables of different sorts attached
           to the same environment, there can only be one sort of
           variable bound by a given binder *)
        assert (b_sort = sort);
        let tyvars =
          List.fold_left (fun vs i -> vset_union vs vars.(i))
            VSnil b_vars in
        (match bs with
         | [] -> cons_typ pol tyvars cons
         | bvars -> Tcons { tyvars; cons; bvars; pol })
     | bvars ->
        (* Other bound variables *)
        Tcons { tyvars; cons; bvars; pol }
     end
  | Tpoly_pos (bounds, body) ->
     let ix = ix + 1 in
     Tpoly_pos (Array.map (fun (l,u) -> open_typ sort vars ix l,
                                        open_typ sort vars ix u) bounds,
                open_typ sort vars ix body)
  | Tpoly_neg (bounds, flow, body) ->
     let ix = ix + 1 in
     Tpoly_neg (Array.map (fun (l, u) -> open_typ sort vars ix l,
                                         open_typ sort vars ix u) bounds,
                flow,
                open_typ sort vars ix body)
  

let is_styp = function
  | Tsimp s -> s
  | _ -> assert false

(* Well-formedness checks.
   The wf_foo functions check for local closure also. *)

let rec wf_cons pol env wf = function
  | Ident | Annih -> ()
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
  | Tcons { tyvars; cons; bvars; pol = pol' } ->
     assert (pol = pol');
     assert (bvars = []); (* locally closed *)
     wf_vset pol env tyvars;
     wf_cons pol env wf_typ cons
  | Tsimp s ->
     wf_styp pol env s
  | Tpoly_pos (vars, body) ->
     assert (pol = Pos);
     (* create flexible variables *)
     let env = env_cons env Egen in
     let tyvars = match env with Env_cons { tyvars; _ } -> tyvars | _ -> assert false in (* uglllyyyy. *)
     let nvars = Array.length vars in
     for _i = 0 to nvars - 1 do
       Vector.push tyvars { pos = cons_styp Pos VSnil Ident;
                            neg = cons_styp Neg VSnil Ident }
     done;
     let vsets = Array.init nvars (fun i ->
       VScons { env; sort = Flexible; vars = [i]; rest = VSnil }) in
     for i = 0 to nvars - 1 do
       let v = Vector.get tyvars i in
       let (pos, neg) = vars.(i) in
       v.pos <- is_styp (open_typ Flexible vsets 0 pos);
       v.neg <- is_styp (open_typ Flexible vsets 0 neg);
     done;
     wf_flexvars env tyvars;    (* check ε-invariant *)
     wf_typ Pos env (open_typ Flexible vsets 0 body)
  | Tpoly_neg (bounds, flow, body) ->
     assert (pol = Neg);
     let nvars = Array.length bounds in
     let vars = Array.init nvars (fun _ ->
       { rig_lower = cons_styp Neg VSnil Annih;
         rig_upper = cons_styp Pos VSnil Annih }) in
     let env_entry = Erigid { vars; flow } in
     let env = env_cons env env_entry in
     let vsets = Array.init nvars (fun i ->
       VScons { env; sort = Rigid; vars = [i]; rest = VSnil }) in
     for i = 0 to nvars - 1 do
       let (lower, upper) = bounds.(i) in
       vars.(i) <- { rig_lower = is_styp (open_typ Rigid vsets 0 lower);
                     rig_upper = is_styp (open_typ Rigid vsets 0 upper) }
     done;
     wf_env_entry env env_entry;
     wf_typ Neg env (open_typ Rigid vsets 0 body)

and wf_vset pol env_ext = function
  | VSnil -> ()
  | VScons { env; sort; vars; rest } ->
     assert_env_prefix env env_ext;
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
