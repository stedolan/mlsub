module IntMap = Map.Make (struct type t = int let compare = compare end)
module StrMap = Map.Make (struct type t = string let compare = compare end)

(* Later, maybe intern these? *)
type symbol = string
module SymMap = Map.Make (struct type t = symbol let compare = compare end)


let fresh_id =
  let next = ref 0 in
  fun () -> let r = !next in incr next; r

type polarity = Pos | Neg
let polneg = function Pos -> Neg | Neg -> Pos

type generalisation_status = Polytype | Monotype

(* Head type constructors *)
type 'a cons_head =
  (* Underconstrained. Might be anything. Identity of meet/join.
     (⊤ if Neg, ⊥ if Pos *)
  | Ident
  (* Overconstrained. Must be everything. Annihilator of meet/join.
     (⊥ if Neg, ⊤ if Pos *)
  | Annih
  | Func of 'a * 'a
  | Record of 'a StrMap.t
  | Abs of symbol * env (* must refer to the most recent addition *)
  (* ... abstract type constructors ... *)

(* Possibly-nested type constructors. FIXME: optimise cons when it has no subterms? *)
and constr =
  { stypes: vset; cons: constr cons_head }

(* Typing environment *)
and env =
  | Env_empty
  | Env_cons of { entry : env_entry; level : int; rest : env }

(* Entries in the typing environment *)
and env_entry =
  (* Binding x : τ *)
  | EVal of symbol * constr
  (* Abstract type α : [σ, τ] (e.g. from ∀ or local type defn).
     FIXME: allow type parameters here (not inferred in σ, τ, though) *)
  | EType of symbol * constr * constr
  (* Marker for scope of generalisation (let binding) *)
  | EGen

(* Type variables, subject to inference.
   These are mutable: during inference, they become more constrained *)
and tyvar = {
  v_id : int;
  v_pol : polarity;
  mutable v_flow : vset;
  mutable v_cons : constr cons_head;
  v_env : env;
}

(* keyed by ID *)
and vset = tyvar IntMap.t

let flow_union (a : vset) (b : vset) : vset =
  IntMap.union (fun _ a' b' -> assert (a' == b'); Some a') a b

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

let cons_head_env = function
  | Abs (_, env) -> env
  | _ -> Env_empty
(*
let cons (t : stype constr cons_head) : stype constr = match t with
  | (Ident|Annih) as cons -> Cons' { cons; env = Env_empty }
  | Abs (_, env) as cons -> Cons' { cons; env }
  | Func (d, r) as cons ->
     let env = env_max (cons_env d) (cons_env r) in
     (match d, r with
      | (Cons' _ as dc), (Cons' _ as rc) ->
         Cons' { cons = Func (dc, rc); env }
      | _ -> Cons {cons; env})
  | Record fields as cons ->
     let env = StrMap.fold (fun _ c e -> env_max (cons_env c) e) fields Env_empty in
     if StrMap.for_all (fun k c -> is_constant c) fields then
       Cons' { cons = Record (StrMap.map as_constant fields); env }
     else
       Cons { cons; env }
 *)
let cons t =
  { stypes = IntMap.empty; cons = t }
(*
let rec cons_map (f : 'a -> 'b) pol (t : 'a constr) : 'b constr =
  match t with
  | Ret a -> Ret (f a)
  | Cons { cons = (Ident|Annih|Abs _); _ } ->
     (* FIXME: parameters to abstract types *)
     assert false (* should have been Cons' *)
  | Cons { cons = Func (d, r); env } ->
     Cons { cons = Func (cons_map f (polneg pol) d, cons_map f pol r); env }
  | Cons { cons = Record fields; env } ->
     Cons { cons = Record (StrMap.map (cons_map f pol) fields); env }
  | Cons' _ as x -> x
 *)

let flow env =
  let p =
    { v_id = fresh_id ();
      v_pol = Pos;
      v_env = env;
      v_cons = Ident;
      v_flow = IntMap.empty }
  and n =
    { v_id = fresh_id ();
      v_pol = Neg;
      v_env = env;
      v_cons = Ident;
      v_flow = IntMap.empty } in
  p.v_flow <- IntMap.singleton n.v_id n;
  n.v_flow <- IntMap.singleton p.v_id p;
  (n,p)

let rec join pol (s : constr) (t : constr) =
  { stypes = flow_union s.stypes t.stypes;
    cons = join_cons pol s.cons t.cons }
and join_cons pol s t =
  match s, t, pol with
  (* top/bottom *)
  | Ident, x, _ | x, Ident, _ -> x
  | Annih, _, _ | _, Annih, _ -> Annih
  (* incompatible types *)
  | Record _, Func _, _
  | Func _, Record _, _ ->
     Annih
  (* FIXME not implemented *)
  | Abs _, _, _ | _, Abs _, _ -> failwith "unimplemented"
  (* Functions *)
  | Func (sd, sr), Func (td, tr), pol ->
     Func (join (polneg pol) sd td, join pol sr tr)
  (* Records *)
  | Record sf, Record tf, Pos ->
     (* upper bound - intersection of fields *)
     Record (StrMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | _ -> None) sf tf)
  | Record sf, Record tf, Neg ->
     (* lower bound - union of fields *)
     Record (StrMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | (Some _ as x), None | None, (Some _ as x) -> x
       | None, None -> None) sf tf)



(* FIXME rectypes :( :( :( *)
let rec biunify p n =
  p.stypes |> IntMap.iter (fun _ v ->
    v.v_flow <- flow_union v.v_flow n.stypes;
    v.v_cons <- join_cons Neg v.v_cons n.cons);
  n.stypes |> IntMap.iter (fun _ v ->
    v.v_flow <- flow_union v.v_flow p.stypes;
    v.v_cons <- join_cons Pos v.v_cons p.cons);
  match p.cons, n.cons with
  | Ident, _
  | _, Ident -> ()
  | Annih, Annih -> ()
  | Annih, _
  | _, Annih
  | Func _, Record _
  | Record _, Func _ -> failwith "type error"
  | Abs _, _ | _, Abs _ -> failwith "unimplemented"
  | Func (d1, r1), Func (d2, r2) ->
     biunify d2 d1;
     biunify r1 r2
  | Record f1, Record f2 ->
     f2 |> StrMap.iter (fun k t2 ->
       match StrMap.find k f1 with
       | t1 -> biunify t1 t2
       | exception Not_found -> failwith "type error on record")





type tyexp =
  | Tcons of vset * tyexp cons_head
  | Tforall of tyexp * tyexp * tyexp


(*


(* Flow edge optimisation:
   We should certainly do this later during gen,
   but should we do easy cases during merge?
   when we set t_cons to Annih, it's valid to also set t_flow to empty.
   Maybe later *)

(* FIXME: verify that uses of merge (in join, biunify) preserve bipartite-ness *)

(* All of the below ignores environments for now *)

(* s.t_cons := s.t_cons + t.t_cons ? *)
let rec merge s t =
  (* First, special handling for some easy cases *)
  match deconstr s.t_cons, deconstr t.t_cons with
  | C Ident, _ -> s.t_cons <- Ret t
  | C Annih, _ -> (* No need for flow edges on Annih *) ()
  (* Next two cases might be redundant *)
  | _, C Ident -> s.t_flow <- flow_union s.t_flow t.t_flow
  | _, C Annih -> (* No need for flow edges on Annih *) s.t_cons <- cons Annih
  | _, _ -> merge1 s t

(* General case of merge *)

(* FIXME: this ruins bipartite property. Fix! *)
and merge1 s t =
  (* follow epsilon (Ret) edges until t yields a constr.
     if we find an epsilon-cycle, it's Ident (since mu a . a = bot, the lpp of id) *)
  (* I could path-compress at this point. Is that a good idea?
     Seems more elegant than cycle detection. *)
  let rec follow_eps visited t =
    assert (t.t_pol = s.t_pol);
    assert (t.t_gen = Monotype && s.t_gen = Monotype);
    (* This is O(n^2) and could be faster. OTOH, long eps-chains are hard to construct? *)
    if List.memq t visited then Ident
    else begin
      s.t_flow <- flow_union s.t_flow t.t_flow;
      follow_eps_cons visited t
    end
  and follow_eps_cons visited t =
    match deconstr t.t_cons with
    | R t' -> follow_eps (t :: visited) t'
    | C tc -> tc in
  match follow_eps_cons [] s with
  | Ident -> s.t_cons <- Ret t
  | Annih -> ()
  | sc ->
     let tc = follow_eps [] t in
     s.t_cons <- join_cons_head s.t_pol sc tc

and join_cons_head pol s t =
  match s, t, pol with
  (* top/bottom *)
  | Ident, x, _ | x, Ident, _ -> cons x
  | Annih, _, _ | _, Annih, _ -> cons Annih
  (* incompatible types *)
  | Record _, Func _, _
  | Func _, Record _, _ ->
     cons Annih
  (* FIXME not implemented *)
  | Abs _, _, _ | _, Abs _, _ -> failwith "unimplemented"
  (* Functions *)
  | Func (sd, sr), Func (td, tr), pol ->
     cons (Func (join_constr (polneg pol) sd td, join_constr pol sr tr))
  (* Records *)
  | Record sf, Record tf, pol ->
     failwith "unimplemented"

(* This is a DFA product, in general.
   It needs a memo table *)
and join_constr pol s t =
  match deconstr s, deconstr t, pol with
  | C s, C t, pol -> join_cons_head pol s t
  | s, t, pol ->
     let r =
       { t_id = fresh_id ();
         t_pol = pol;
         t_cons = cons Ident;
         t_gen = Monotype
     let s' =
       { t_id = fresh_id ();
         t_pol = pol;
         t_cons = cons Ident;
         t_gen = Monotype; (* FIXME *)
         t_env = Env_empty; (* FIXME *)
         t_flow = IntMap.empty } in
     merge s' s;
     
     


(*
  match deconstr s.t_cons, deconstr t with
  (* top / bottom *)
  | C Ident, _ -> s.t_cons <- t
  | C Annih, _ -> ()
  | _, C Ident -> ()
  | _, C Annih -> s.t_cons <- cons Annih

  (* incompatible types *)
  | C (Func _), C (Record _)
  | C (Record _), C (Func _) ->
     s.t_cons <- cons Annih

  (* functions *)
  | C (Func (sd, dr)), C (Func (td, tr)) ->
 *)     




(* t := t + s *)
let rec merge t s =
  assert (t.t_pol = s.t_pol);
  assert (t.t_gen = Monotype && s.t_gen = Monotype);
  (* What if a subterm of t has a environment that's a strict prefix of s?
     Should we strengthen? What does the environment mean, anyway? *)
  ()
(*

How do I do scope tracking?

Γ, x : τ⁻ ⊢ ...

RHS mentions x, we constrain σ⁺ ≤ τ⁻
Add flow edges as usual.
Later, come to generalise. Why can't we generalise?

It's only interesting to generalise when a variable is bound.
Polymorphism only matters when something's used twice.
("Binding" has to include proj₁ of Σ-types here)

OK, so let's add a context marker for whenever we generalise.

Γ, * ⊢ ...

During generalisation

Γ ::= ε | Γ, x : A | Γ, α : [σ⁺ ≤ α ≤ τ⁻]

α ≤ τ⁻
weaken to
σ⁺ ≤ α ≤ τ⁺



 *)

let flow () = (1,2)
 *)
