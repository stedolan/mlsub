(* Core definitions used by the typechecker *)

module IntMap = Map.Make (struct type t = int let compare = compare end)
module StrMap = Map.Make (struct type t = string let compare = compare end)

(* Later, maybe intern these? *)
type symbol = string
module SymMap = Map.Make (struct type t = symbol let compare = compare end)

type polarity = Pos | Neg

(* Head type constructors *)
type 'a cons_head =
  (* Underconstrained. Might be anything. Identity of meet/join.
     (⊤ if Neg, ⊥ if Pos *)
  | Ident
  (* Overconstrained. Must be everything. Annihilator of meet/join.
     (⊥ if Neg, ⊤ if Pos *)
  | Annih
  (* Positional elements are encoded as field names "0", "1", etc. *)
  | Record of 'a StrMap.t
  | Func of 'a StrMap.t * 'a
  | Abs of symbol * envref (* must refer to the most recent addition *)

and envref =
  | Free of env
  | Bound of int (* de Bruijn index *)

(* Simple types (subject to inference).
   Each styp contains no Bound variables *)
and styp =
  { tyvars: vset; cons: styp cons_head }

(* General types (checked / synthesised) *)
and typ =
  | Tcons of vset * typ cons_head
  (* FIXME: maybe forall with typ bounds is OK,
     as long as we don't infer it? *)
  | Tforall of (styp * styp) StrMap.t * typ

(* Typing environment *)
and env =
  | Env_empty
  | Env_cons of { entry : env_entry; level : int; rest : env }

(* Entries in the typing environment *)
and env_entry =
  (* Binding x : τ *)
  | Eval of symbol * typ
  (* Abstract types α : [σ, τ] (mutually recursive)
     (e.g. from ∀ or local type defn).
     FIXME: allow type parameters here (not inferred in σ, τ, though) *)
  | Etype of (typ * typ) StrMap.t
  (* Marker for scope of generalisation (let binding) *)
  | Egen of { mutable vars : tyvar list }

(*
(* Type variables, subject to inference.
   These are mutable: during inference, they become more constrained *)
and tyvar = {
  v_id : int;
  v_pol : polarity;
  mutable v_flow : vset;
  mutable v_cons : constr cons_head;
  v_env : env;
}
 *)

and tyvar = {
  v_id: int;
  v_env : env;
  mutable v_pos : styp;
  mutable v_neg : styp;
}

(* keyed by v_id *)
and vset = tyvar IntMap.t


