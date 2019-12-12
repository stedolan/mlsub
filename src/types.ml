open Typedefs

let polneg = function Pos -> Neg | Neg -> Pos

let intfail s = failwith ("internal error: " ^ s)



let open_cons ix env open_a = function
  (* FIXME: this could be optimised with knowledge of type support *)
  | Ident -> Ident
  | Annih -> Annih
  | Record fields ->
     Record (StrMap.map (open_a ix env) fields)
  | Func (args, res) ->
     Func (StrMap.map (open_a ix env) args, open_a ix env res)
  | Abs (_, Bound k) when k > ix ->
     (* Can only open the outermost binder group *)
     assert false
  | Abs (s, Bound k) when k = ix ->
     Abs (s, Free env)
  | Abs _ as abs ->
     abs

let rec open_typ ix env = function
  | Tcons (vset, cons) ->
     Tcons (vset, open_cons ix env open_typ cons)
  | Tforall (vars, body) ->
     Tforall (vars, open_typ (ix+1) env body)


(* FIXME: doing this lazily (via a Tsimple ctor) might make
   generalisation / instantiation faster in the absence of bound vars *)
let rec typ_of_styp { tyvars; cons } =
  Tcons (tyvars, map_head typ_of_styp cons)

let assert_wf_envref env = function
  | Free env' ->
     assert_env_prefix env' env;
     env'
  | Bound _ ->
     assert false

(* Also checks that the type is locally closed *)
let assert_wf_cons env wf = function
  | Ident | Annih -> ()
  | Record fields ->
     StrMap.iter (fun _ t -> wf env t) fields
  | Func (args, res) ->
     StrMap.iter (fun _ t -> wf env t) args;
     wf env res
  | Abs (s, eref) ->
     let env' = assert_wf_envref env eref in
     begin match env' with
     | Env_cons { entry = Etype defs; _ } ->
        assert (StrMap.mem s defs)
     | _ -> assert false
     end

let rec assert_wf_typ env = function
  | Tcons (tyvars, cons) ->
     IntMap.iter (fun _ v -> assert_wf_tyvar env v) tyvars;
     assert_wf_cons env assert_wf_typ cons
  | Tforall (vars, body) ->
     let ext = Etype (StrMap.map (fun (l, u) ->
                   (typ_of_styp l, typ_of_styp u)) vars) in
     let env = env_cons env ext in
     let body = open_typ 0 env body in
     assert_wf_typ env body

and assert_wf_tyvar env v =
  assert_env_prefix v.v_env env;
  assert_wf_styp env v.v_pos;
  assert_wf_styp env v.v_neg

and assert_wf_styp env { tyvars; cons } =
  IntMap.iter (fun _ v -> assert_wf_tyvar env v) tyvars;
  assert_wf_cons env assert_wf_styp cons

let rec assert_wf_env = function
  | Env_empty -> ()
  | Env_cons { entry; level; rest } as env ->
     assert (level = env_level rest + 1);
     assert_wf_env_entry env entry;
     assert_wf_env rest

and assert_wf_env_entry env = function
  | Eval (_, typ) -> assert_wf_typ env typ
  | Etype defs ->
     (* FIXME should there be a strict positivity / contractivity check? *)
     defs |> StrMap.iter (fun _ (l,u) ->
       assert_wf_typ env l;
       assert_wf_typ env u)
  | Egen v ->
     List.iter (assert_wf_tyvar env) v.vars




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
  { tyvars = IntMap.empty; cons = t }
let tcons t =
  Tcons (IntMap.empty, t)
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
(*
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
 *)


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
