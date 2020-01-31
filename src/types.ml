open Typedefs

let intfail s = failwith ("internal error: " ^ s)

(* join Pos = ⊔, join Neg = ⊓ (meet) *)
let rec join pol (s : styp) (t : styp) =
  assert (s.pol = pol && t.pol = pol);
  { tyvars = vset_union s.tyvars t.tyvars;
    cons = join_cons pol s.cons t.cons;
    pol }
and join_cons pol s t =
  match s, t with
  (* top/bottom *)
  | Bot, x | x, Bot ->
     (match pol with Pos -> x | Neg -> Bot)
  | Top, x | x, Top ->
     (match pol with Neg -> x | Pos -> Top)
  (* equal base types *)
  | Bool, Bool -> Bool
  | Int, Int -> Int
  | String, String -> String
  (* incompatible types *)
  | Bool, (Record _|Func _|Int|String) | (Record _|Func _|Int|String), Bool
  | Int, (Record _|Func _|String) | (Record _|Func _|String), Int
  | String, (Record _|Func _) | (Record _|Func _), String
  | Record _, Func _
  | Func _, Record _ ->
     annih pol
  (* Functions *)
  | Func (sd, sr), Func (td, tr) ->
     begin match join_fields (polneg pol) sd td with
     | Some args -> Func (args, join pol sr tr)
     | None -> annih pol
     end
  (* Records *)
  | Record sf, Record tf ->
     begin match join_fields pol sf tf with
     | Some fs -> Record fs
     | None -> annih pol
     end
and join_fields pol sf tf =
  match pol with
  | Neg ->
     (* lower bound - union of fields *)
     let same = ref true in
     let rec union_pos sps tps =
       match sps, tps with
       | [], [] -> []
       | sp :: sps, tp :: tps -> join pol sp tp :: union_pos sps tps
       | xs, [] | [], xs -> same := false; xs in
     let fpos = union_pos sf.fpos tf.fpos in
     let fnames = sf.fnames @ 
       List.filter (fun k -> not (StrMap.mem k tf.fnamed)) tf.fnames in
     let fnamed = StrMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | (Some _ as x), None | None, (Some _ as x) ->
          same := false;
          x
       | None, None -> None) sf.fnamed tf.fnamed in
     begin match sf.fopen, tf.fopen, !same with
     | `Open, `Open, _ ->
        Some {fpos; fnames; fnamed; fopen = `Open}
     | _, _, true ->
        (* Not both open, but same fields *)
        Some {fpos; fnames; fnamed; fopen = `Closed}
     | _, _, false ->
        (* Neither both open nor same fields *)
        None
     end
  | Pos ->
     (* upper bound - intersection of fields *)
     let same = ref true in
     let rec inter_pos sps tps =
       match sps, tps with
       | [], [] -> []
       | sp :: sps, tp :: tps -> join pol sp tp :: inter_pos sps tps
       | _, [] | [], _ -> same := false; [] in
     let fpos = inter_pos sf.fpos tf.fpos in
     let fnames = List.filter (fun k -> StrMap.mem k tf.fnamed) sf.fnames in
     let fnamed = StrMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | None, Some _ | Some _, None ->
          same := false;
          None
       | _ -> None) sf.fnamed tf.fnamed in
     begin match sf.fopen, tf.fopen, !same with
     | `Closed, `Closed, true ->
        Some {fpos; fnames; fnamed; fopen = `Closed }
     | _, _, _ ->
        Some {fpos; fnames; fnamed; fopen = `Open }
     end

type conflict_reason =
  | Incompatible
  | Missing of [`Named of string|`Positional]
  | Extra of [`Fields|`Named of string|`Positional]


(* pol = Pos: <=, pol = Neg: >= *)
let subtype_cons_fields pol af bf f =
  let extra_errs =
    match pol, af.fopen, bf.fopen with
    | Pos, `Open, `Closed 
    | Neg, `Closed, `Open -> [Extra `Fields]
    | _ -> [] in
  let extra_errs =
    match pol, af.fopen, bf.fopen with
    | Pos, _, `Closed ->
       (* check dom a ⊆ dom b *)
       let extra_errs =
         if List.length af.fpos > List.length bf.fpos then
           Extra `Positional :: extra_errs else extra_errs in
       List.fold_right (fun k acc ->
         match StrMap.find k bf.fnamed with
         | exception Not_found -> Extra (`Named k) :: acc
         | _ -> acc) af.fnames extra_errs
    | Neg, `Closed, _ ->
       (* check dom b ⊆ dom a *)
       let extra_errs =
         if List.length bf.fpos > List.length af.fpos then
           Extra `Positional :: extra_errs else extra_errs in
       List.fold_right (fun k acc ->
         match StrMap.find k af.fnamed with
         | exception Not_found -> Extra (`Named k) :: acc
         | _ -> acc) bf.fnames extra_errs
    | _ -> extra_errs in

  let rec subtype_pos aps bps acc = match aps, bps, pol with
    | [], [], _ -> acc
    | _, [], Pos | [], _, Neg -> acc (* extra fields handled above *)
    | [], _, Pos | _, [], Neg -> Missing `Positional :: acc
    | ap :: aps, bp :: bps, pol -> f pol ap bp @ subtype_pos aps bps acc in
  let errs = subtype_pos af.fpos bf.fpos extra_errs in
  match pol with
  | Pos ->
    StrMap.fold (fun k b acc ->
      match StrMap.find k af.fnamed with
      | exception Not_found -> Missing (`Named k) :: acc
      | a -> f pol a b @ acc) bf.fnamed errs
  | Neg ->
     StrMap.fold (fun k a acc ->
      match StrMap.find k bf.fnamed with
      | exception Not_found -> Missing (`Named k) :: acc
      | b -> f pol a b @ acc) af.fnamed errs

let subtype_cons pol a b f =
  match pol, a, b with
  | _, Bool, Bool -> []
  | _, Int, Int -> []
  | _, String, String -> []
  | pol, Func (args, res), Func (args', res') ->
     subtype_cons_fields (polneg pol) args args' f @ f pol res res'
  | pol, Record fs, Record fs' ->
     subtype_cons_fields pol fs fs' f
  | Pos, Bot, _
  | Neg, _, Bot
  | Pos, _, Top
  | Neg, Top, _ -> []
  | _,_,_ -> [Incompatible]


(* Computes epsilon-closure of a type *)
let eps_closure env pol t =
  let seen = Hashtbl.create 10 in
  let rec accum_v acc i =
    if Hashtbl.mem seen i then acc
    else begin
      Hashtbl.add seen i ();
      let flexvar = env_flexvar env i in
      let t =
        match pol with Pos -> flexvar.pos | Neg -> flexvar.neg in
      accum acc t
    end
  and accum acc { tyvars; cons; pol = pol' } =
    assert (pol = pol');
    List.fold_left accum_v
      (join_cons pol acc cons)
      (vset_lookup env Flexible tyvars) in
  accum (ident pol) t
  

(* Given a styp well-formed in ext,
   find the best approximation well-formed in the shorter environment env.

   Pos types are approximated from above and Neg types from below. *)
let rec approx_styp env ext pol' ({ tyvars=_; cons=_; pol } as orig) =
  assert_env_prefix env ext;
  wf_env ext;
  wf_styp pol' ext orig;
  assert (pol = pol');
  if env_equal env ext then orig
  else
    failwith "approx unimplemented"
(*
    let cons = map_head pol (approx_styp env ext) cons in
    let tyvars = asdf in
    { tyvars; cons; pol }
 *)


(* 
  flex_closure pol acc env vars, where
    env ≤ venv
    env ⊢pol acc, but acc has no vars before venv flex at toplevel
    vars ⊆ venv.flex
  returns a styp s, s.t. env ⊢pol s
  where s is the join of acc and all of vars bounds
  but s does not have toplevel refs to any flexible vars at level env
  (wtf)
 *)
let flex_closure pol env acc venv vars =
  assert_env_prefix venv env;
  wf_styp pol env acc;
  assert (snd (styp_uncons venv Flexible acc) = []);
  let seen = Hashtbl.create 10 in
  let rec go acc vars =
    List.fold_left (fun acc v ->
      if Hashtbl.mem seen v then acc else begin
      Hashtbl.add seen v ();
      let v = env_flexvar venv v in
      let t = match pol with Pos -> v.pos | Neg -> v.neg in
      let t, newvs = styp_uncons venv Flexible t in
      join pol t (go acc newvs) end) acc vars in
  let res = go acc vars in
  wf_styp pol env res;
  assert (snd (styp_uncons venv Flexible res) = []);
  res
     

let pol_flip f pol a b =
  match pol with Pos -> f a b | Neg -> f b a

let rec subtype_styp env p n =
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  match p.tyvars, n.tyvars with
  | VSnil, VSnil ->
     subtype_cons Pos p.cons n.cons
       (pol_flip (subtype_styp env))
  | VScons v, VSnil
  | VSnil, VScons v ->
     subtype_styp_vars env p n v.env v.sort
  | VScons pv, VScons nv when
       pv.env == nv.env ->
     let vsort = min pv.sort nv.sort in (* i.e. Flex if either is *)
     subtype_styp_vars env p n pv.env vsort
  | VScons pv, VScons nv when
      env_level pv.env > env_level nv.env ->
     subtype_styp_vars env p n pv.env pv.sort
  | VScons _pv, VScons nv
      (* env_level pv.env < env_level nv.env *) ->
     subtype_styp_vars env p n nv.env nv.sort

and subtype_styp_vars env p n venv vsort =
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  assert_env_prefix venv env;
  let (prest, pvs) = styp_uncons venv vsort p in
  let (nrest, nvs) = styp_uncons venv vsort n in
  match vsort with
  | Flexible ->
     pvs |> List.iter (fun pvi ->
       let v = env_flexvar venv pvi in
       v.neg <- join Neg v.neg (approx_styp venv env Neg n));
     nvs |> List.iter (fun nvi ->
       let v = env_flexvar venv nvi in
       v.pos <- join Pos v.pos (approx_styp venv env Pos p));
     subtype_styp env
       (flex_closure Pos env prest venv pvs)
       (flex_closure Neg env nrest venv nvs)
  | Rigid ->
     (* this is a load of bollocks *)
     assert false


(* Give a typ well-formed in ext, approx in env.
   Same as approx_styp *)
let rec approx env ext pol t =
  assert_env_prefix env ext;
  wf_env ext;
  wf_typ pol ext t;
  match t with
  | Tpoly_neg (bounds, flow, body) ->
     assert (pol = Neg);
     let (ext, vsets) = enter_poly_neg ext bounds flow in
     approx env ext pol (open_typ Rigid vsets 0 Neg body)
  | Tpoly_pos (vars, body) ->
     assert (pol = Pos);
     let (ext, vsets) = enter_poly_pos ext vars in
     approx env ext pol (open_typ Flexible vsets 0 Pos body)
  | Tsimple s ->
     approx_styp env ext pol (is_styp s)
  | Tcons cons ->
     cons_styp pol VSnil (map_head pol (approx env ext) cons)


(* Always Pos <= Neg *)
let rec subtype env p n =
  wf_env env;
  wf_typ Pos env p;
  wf_typ Neg env n;
  match p, n with
  | Tpoly_neg _, _
  | _, Tpoly_pos _ -> intfail "malformed"

  (* FIXME: some sort of coherence check needed *)
  | p, Tpoly_neg (bounds, flow, body) ->
     let env, vsets = enter_poly_neg env bounds flow in
     subtype env p (open_typ Rigid vsets 0 Neg body)
  | Tpoly_pos(vars, body), n ->
     let env, vsets = enter_poly_pos env vars in
     subtype env (open_typ Flexible vsets 0 Pos body) n

  | Tsimple p, Tsimple n ->
     subtype_styp env (is_styp p) (is_styp n)
  | _, Tsimple n ->
     subtype_styp env (approx env env Pos p) (is_styp n)
  | Tsimple p, _ ->
     subtype_styp env (is_styp p) (approx env env Neg n)

  | Tcons s, Tcons t ->
     subtype_cons Pos s t 
       (pol_flip (subtype env))

let fill_template env pol s t =
  wf_typ pol env s;
  if !t <> cons_typ pol (ident pol) then
    failwith "fill_template: nonlinear template";
  t := s

let rec freshen_template env pol (t : template) : styp =
  wf_template pol env t;
  match t with
  | Tm_typ t ->
     approx env env pol t
  | Tm_cons t ->
     cons_styp pol VSnil (map_head pol (freshen_template env) t)
  | Tm_unknown t ->
     let v = fresh_flexible env in
     fill_template env (polneg pol)
       (Tsimple (Tstyp_simple
         (cons_styp (polneg pol) v (ident (polneg pol))))) t;
     cons_styp pol v (ident pol)

(* All callers use a Pos typ and a Neg template,
   but recursive calls may swap them *)
    
let rec match_type env pol (p : typ) (t : template) =
  wf_env env;
  wf_typ pol env p;
  wf_template (polneg pol) env t;
  match t with
  | Tm_typ t ->
     pol_flip (subtype env) pol p t
  | Tm_unknown t ->
     fill_template env pol p t;
     []
  | Tm_cons t ->
     match_type_cons env pol p t

and match_type_cons env pol (p : typ) (t : template cons_head) =
  match p with
  | Tcons cons ->
     subtype_cons pol cons t (match_type env)
  | Tpoly_neg _ ->
     (* Is this reachable? *)
     assert false
  | Tpoly_pos (vars, body) ->
     (* t is not ∀, so we need to instantiate p *)
     assert (pol = Pos);
     let vsets = instantiate_flexible env vars in
     let body = open_typ Flexible vsets 0 Pos body in
     match_type_cons env pol body t
  | Tsimple p ->
     match_styp_cons env pol (is_styp p) t

and match_styp env pol (p : styp) (t : template) =
  match t with
  | Tm_typ _
  | Tm_unknown _ ->
     match_type env pol (Tsimple (Tstyp_simple p)) t
  | Tm_cons t ->
     match_styp_cons env pol p t

and match_styp_cons env pol (p : styp) (t : template cons_head) =
  match p.tyvars with
  | VSnil ->
     (* Optimisation in the case of no flow *)
     subtype_cons pol p.cons t (match_styp env)
  | _ ->
     let t = freshen_template env (polneg pol) (Tm_cons t) in
     pol_flip (subtype_styp env) pol p t

(*



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
 *)
