open Typedefs

let intfail s = failwith ("internal error: " ^ s)

let fresh_id =
  let next = ref 0 in
  fun () -> let r = !next in incr next; r


let fresh_var env =
  let v =
    { v_id = fresh_id ();
      v_env = env;
      v_pos = { tyvars = IntMap.empty; cons = Ident };
      v_neg = { tyvars = IntMap.empty; cons = Ident } } in
  let rec add_to_gen_point = function
    | Env_empty ->
       intfail "inference variable created outside generalisation scope"
    | Env_cons { entry; rest; _ } ->
       match entry with
       | Eval _ | Etype _ -> add_to_gen_point rest
       | Egen gen ->
          gen.vars <- v :: gen.vars in
  add_to_gen_point env;
  v

(* join Pos = ⊔, join Neg = ⊓ (meet) *)
let rec join pol (s : styp) (t : styp) =
  { tyvars = vset_union s.tyvars t.tyvars;
    cons = join_cons pol s.cons t.cons }
and join_cons pol s t =
  match s, t with
  (* top/bottom *)
  | Ident, x | x, Ident -> x
  | Annih, _ | _, Annih -> Annih
  (* incompatible types *)
  | Record _, Func _
  | Func _, Record _ ->
     Annih
  (* FIXME not implemented *)
  | Abs _, _ | _, Abs _ -> failwith "unimplemented"
  (* Functions *)
  | Func (sd, sr), Func (td, tr) ->
     Func (join_fields (polneg pol) sd td, join pol sr tr)
  (* Records *)
  | Record sf, Record tf ->
     Record (join_fields pol sf tf)
and join_fields pol ss tt =
  match pol with
  | Neg ->
     (* lower bound - union of fields *)
     StrMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | (Some _ as x), None | None, (Some _ as x) -> x
       | None, None -> None) ss tt
  | Pos ->
     (* upper bound - intersection of fields *)
     StrMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | _ -> None) ss tt

let bound pol v =
  match pol with
  | Pos -> v.v_pos
  | Neg -> v.v_neg

(* Computes epsilon-closure of a type *)
let closure pol t =
  let rec go vars acc =
    IntMap.fold (fun id v ({ tyvars; cons } as acc) ->
      if IntMap.mem id tyvars then acc else
        let tyvars = IntMap.add id v tyvars in
        let {tyvars = v_tyvars; cons = v_cons} = bound pol v in
        let cons = join_cons pol cons v_cons in
        go v_tyvars {tyvars; cons}) vars acc in
  let { tyvars; cons } = t in
  go tyvars { tyvars = IntMap.empty; cons }


(* FIXME rectypes :( :( :( *)
let rec biunify p n =
  (*
  (* This does head-expansion! Arrrrghghghghgh! *)
  p.tyvars |> IntMap.iter (fun _ v ->
    v.v_flow <- flow_union v.v_flow n.tyvars;
    v.v_cons <- join_cons Neg v.v_cons n.cons);
  n.tyvars |> IntMap.iter (fun _ v ->
    v.v_flow <- flow_union v.v_flow p.tyvars;
    v.v_cons <- join_cons Pos v.v_cons p.cons);
   *)
  let { tyvars = p_vars; cons = p_cons } = closure Pos p in
  let { tyvars = n_vars; cons = n_cons } = closure Neg n in
  (* FIXME: optimisation: maintain the episilon-invariant between
     type variables from the same EGen, then we can skip some of the below *)
  p_vars |> IntMap.iter (fun _ v -> v.v_neg <- join Neg v.v_neg n);
  n_vars |> IntMap.iter (fun _ v -> v.v_pos <- join Pos v.v_pos p);
  match p_cons, n_cons with
  | Ident, _
  | _, Ident -> ()
  | Annih, Annih -> ()
  | Annih, _
  | _, Annih
  | Func _, Record _
  | Record _, Func _ -> failwith "type error"
  | Abs _, _ | _, Abs _ -> failwith "unimplemented"
  | Func (d1, r1), Func (d2, r2) ->
     biunify_fields d2 d1;
     biunify r1 r2
  | Record f1, Record f2 ->
     biunify_fields f1 f2
and biunify_fields pf nf =
  nf |> StrMap.iter (fun k n ->
    match StrMap.find k pf with
    | p -> biunify p n
    | exception Not_found -> failwith ("type error on field " ^ k))


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


  (* 

What can go in the environment? This is the main problem.
(This will eventually match what can go in records/ modules)

  - Values with a simple type
  - Values with a weird type
  - Generalisation points (with list of tyvars)
  - Abstract types with upper and lower bounds

Are the upper and lower bounds simple types?
In forall yes, in environments not necessarily.

This allows abstract types, like from another module?
Having a large type for one of those seems useful

   type t <= { foo : [A](A) => A }
   let f (x : t) = (x.foo)(42)

This sounds like abstract type bounds should be general types.
The forall is predicative, but the predicativity shows up only in instantiation.
How does this affect smallness?

 *)

let rec try_styp_of_typ = function
  | Tforall _ ->
     failwith "not a simple type"
  | Tcons (tyvars, cons) ->
     { tyvars; cons = map_head try_styp_of_typ cons }
