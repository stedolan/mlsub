open Tuple_fields
open Typedefs

exception Internal of string
let intfail s = raise (Internal s)
let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

(* join Pos = ⊔, join Neg = ⊓ (meet) *)
let rec join pol (a : styp) (b: styp) =
  match styp_unconsv2 a b with
  | Cons2 { a; b } -> Cons { pol; cons = join_cons pol a b }
  | Vars2 { level; a; va; b; vb } ->
     Free_vars { level; vars = vlist_union va vb; rest = join pol a b }

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
     begin match merge_fields sf tf
       ~left:(fun _ s -> Some s)
       ~right:(fun _ t -> Some t)
       ~both:(fun _ s t -> Some (join pol s t))
       ~extra:(function
         | ((`Closed, `Extra), _)
         | (_, (`Closed, `Extra)) -> raise_notrace Exit
         | (`Open, _), (`Open, _) -> `Open
         | (`Closed, `Subset), (`Closed, `Subset) -> `Closed
         | (`Closed, `Subset), (`Open, _) -> `Closed
         | (`Open, _), (`Closed, `Subset) -> `Closed
       )
     with
     | st -> Some st
     | exception Exit -> None
     end
  | Pos ->
     (* upper bound - intersection of fields *)
     Some (merge_fields sf tf
       ~left:(fun _ _s -> None)
       ~right:(fun _ _t -> None)
       ~both:(fun _ s t -> Some (join pol s t))
       ~extra:(function
         | (`Closed, `Subset), (`Closed, `Subset) -> `Closed
         | _ -> `Open))

type conflict_reason =
  | Incompatible
  | Missing of field_name
  | Extra of [`Fields|`Named of field_name]

(* pol = Pos: <=, pol = Neg: >= *)
(* FIXME: replace with merge_fields *)
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
       List.fold_right (fun k acc ->
         match FieldMap.find k bf.fields with
         | exception Not_found -> Extra (`Named k) :: acc
         | _ -> acc) af.fnames extra_errs
    | Neg, `Closed, _ ->
       (* check dom b ⊆ dom a *)
       List.fold_right (fun k acc ->
         match FieldMap.find k af.fields with
         | exception Not_found -> Extra (`Named k) :: acc
         | _ -> acc) bf.fnames extra_errs
    | _ -> extra_errs in
  match pol with
  | Pos ->
    FieldMap.fold (fun k b acc ->
      match FieldMap.find k af.fields with
      | exception Not_found -> Missing k :: acc
      | a -> f pol k a b @ acc) bf.fields extra_errs
  | Neg ->
     FieldMap.fold (fun k a acc ->
      match FieldMap.find k bf.fields with
      | exception Not_found -> Missing k :: acc
      | b -> f pol k a b @ acc) af.fields extra_errs

let subtype_cons pol a b f =
  match pol, a, b with
  | _, Bool, Bool -> []
  | _, Int, Int -> []
  | _, String, String -> []
  | pol, Func (args, res), Func (args', res') ->
     subtype_cons_fields (polneg pol) args args' (fun pol _fn -> f pol) @ f pol res res'
  | pol, Record fs, Record fs' ->
     subtype_cons_fields pol fs fs' (fun pol _fn -> f pol)
  | Pos, Bot, _
  | Neg, _, Bot
  | Pos, _, Top
  | Neg, Top, _ -> []
  | _,_,_ -> [Incompatible]


let pol_flip f pol a b =
  match pol with Pos -> f a b | Neg -> f b a

let fresh_flexvar env lvl =
  let fv = env_flexvars env lvl in
  Vector.push fv { name = None;
                   pos = styp_trivial Pos;
                   neg = styp_trivial Neg;
                   pos_match_cache = ident Pos;
                   neg_match_cache = ident Neg }

let flow_of_flexvar _env l v =
  let vs = Intlist.singleton v () in
  styp_vars Neg l vs, styp_vars Pos l vs

(* maps (l1, v, pol, l2) -> v' when v' approximates (l1,v) w/ polarity pol *)
type apxcache = (env_level * int * polarity * env_level, int) Hashtbl.t

(* Given a styp well-formed in env,
   find the best approximation well-formed at a shorter level lvl.

   This may require hoisting some flexible variables to lvl.

   Pos types are approximated from above and Neg types from below. *)
let rec approx_styp env apxcache lvl pol ty =
  wf_styp pol env ty;
  ignore (env_at_level env lvl);
  match env with
  | Env_cons { level; _ } when Env_level.equal lvl level -> ty
  | _ ->
  match ty with
  | Bound_var _ -> assert false
  | Cons { pol; cons } ->
     Cons { pol; cons = map_head pol (approx_styp env apxcache lvl) cons }
  | Free_vars { level; vars; rest } ->
     let rest = approx_styp env apxcache lvl pol rest in
     if Env_level.extends level lvl then
       (* can keep *)
       Free_vars { level; vars; rest }
     else
       (* needs approx *)
       vars |> Intlist.to_list |> List.fold_left (fun ty (v, ()) ->
         join pol ty (approx_styp_var env apxcache lvl pol level v)) rest

and approx_styp_var env apxcache lvl pol lvl' v' =
  (* approximate the variable v at (lvl', mark') to (lvl, mark) *)
  assert (Env_level.sort lvl = Esort_flexible);
  assert (Env_level.extends lvl lvl');
  ignore (env_at_level env lvl');
  assert (not (Env_level.equal lvl lvl'));
  match env_entry_at_level env lvl' with
  | Eflexible {vars=flexvars'; _} ->
     let cachekey = (lvl', v', pol, lvl) in
     begin match Hashtbl.find apxcache cachekey with
     | v ->
        styp_var pol lvl v
     | exception Not_found ->
        let v = fresh_flexvar env lvl in
        Hashtbl.add apxcache cachekey v;
        let fv = Vector.get (env_flexvars env lvl) v in
        let fv' = Vector.get flexvars' v' in
        begin match pol with
        | Pos ->
           (* v >= v' *)
           let apx = approx_styp env apxcache lvl Pos fv'.pos in
           fv.pos <- join Pos fv.pos apx;
           (* preserve ε-inv *)
           Intlist.iter (snd (styp_unconsv lvl apx)) (fun ev () ->
             let efv = Vector.get (env_flexvars env lvl) ev in
             efv.neg <- join Neg efv.neg (styp_var Neg lvl v));
           fv'.neg <- join Neg fv'.neg (styp_var Neg lvl v)
        | Neg ->
           (* v <= v' *)
           let apx = approx_styp env apxcache lvl Neg fv'.neg in
           fv.neg <- join Neg fv.neg apx;
           (* preserve ε-inv *)
           Intlist.iter (snd (styp_unconsv lvl apx)) (fun ev () ->
             let efv = Vector.get (env_flexvars env lvl) ev in
             efv.pos <- join Pos efv.pos (styp_var Pos lvl v));
           fv'.pos <- join Pos fv'.pos (styp_var Pos lvl v);
        end;
        styp_var pol lvl v
     end
  | Erigid {names=_; vars; flow=_} ->
     let rv = vars.(v') in
     let bound = match pol with Pos -> rv.rig_upper | Neg -> rv.rig_lower in
     approx_styp env apxcache lvl pol bound
  | _ ->
     failwith "expected variables at this env level"

let approx_styp env apxcache lvl pol ty =
  let res = approx_styp env apxcache lvl pol ty in
  wf_styp pol (env_at_level env lvl) res;
  res
(*

Can I do approx using articulation & articulation caches?
Tricky case is approx of a recursive type.
Suppose Γ, α, ..., β ≤ { foo : β }
and we have α ≤ β
Need to approx β to α's level, I think?


(I). Let's try purely articulation-based approx. Causes head exp, but that's fine here.
    α ≤ β. β: [α, {foo:β}], recurse on bounds.
    α ≤ { foo : β }
    articulate α to { foo : γ }, cache γ in articulation cache
    { foo : γ } ≤ { foo : β }
    γ ≤ β
    expands to
    γ ≤ { foo : β }
    tricky! α's articulation cache does not apply. Hard to ensure termination here.

(II). Separate approx operation.
    Need to approx β to the level of α.
    Introduce β'.
    β' ≤ { foo : γ }, γ ≤ β.
    This is really about caching β. I don't see a good way around that.


*)

  (*
    let cons = map_head pol (approx_styp env ext) cons in
    let ty = join pol { pol; cons; tyvars = VSnil } (approx_vset env pol tyvars) in
    wf_env ext;
    wf_styp pol env ty;
    ty
   *)


let rec flex_closure pol env lvl flexvars (t : styp) vseen vnew =
  wf_styp pol env t;
  (* FIXME head_below wf assert (Intlist.all_below lvl t.tyvars.vs_free); *)
  if Intlist.is_empty vnew then t, vseen
  else begin
    let t = Intlist.to_list vnew |> List.fold_left (fun t (v, ()) ->
      let v = Vector.get flexvars v in
      let bound = match pol with Pos -> v.pos | Neg -> v.neg in
      join pol t bound) t in
    let vseen = Intlist.union (fun _k () () -> ()) vseen vnew in
    (* FIXME use uncons *)
    let t, vnext = styp_unconsv lvl t in
    flex_closure pol env lvl flexvars t vseen (Intlist.remove vnext vseen)
  end
  
(* The termination condition here is extremely tricky, if it's even true *)

(* env ⊢ p ≤ n *)
let rec subtype_styp env (apxcache : apxcache) (p : styp) (n : styp) =
  (* PPrint.(ToChannel.pretty 1. 80 stdout (hardline ^^ group (group (pr_env env ^^ string " ⊢") ^^ break 1 ^^ group (group (pr_styp Pos p) ^^ break 1 ^^ string "≤" ^^ break 1 ^^ group (pr_styp Neg n))) ^^ hardline)); *)
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  match styp_unconsv2 p n with
  | Cons2 { a=p; b=n } ->
     subtype_cons Pos p n (pol_flip (subtype_styp env apxcache))
  | Vars2 { level; a=pcons; va=pvars; b=ncons; vb=nvars } ->
     subtype_styp_vars env apxcache level p n pcons ncons pvars nvars

(* env ⊢ p ⊔ pv ≤ n ⊓ nv, where pv, nv same level, above anything else in p,n *)
and subtype_styp_vars env apxcache lvl orig_p orig_n (p : styp) (n : styp) pvs nvs =
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  match env_entry_at_level env lvl with
  | Eflexible {vars;_} ->
     (* FIXME: avoid some calls to approx_styp for constraints that already hold! *)
     Intlist.iter pvs (fun pv () ->
       let pv = Vector.get vars pv in
       pv.neg <- join Neg pv.neg (approx_styp env apxcache lvl Neg orig_n)
     );
     Intlist.iter nvs (fun nv () ->
       let nv = Vector.get vars nv in
       nv.pos <- join Pos nv.pos (approx_styp env apxcache lvl Pos orig_p)
     );
     wf_env env;
     let clp, _ = flex_closure Pos env lvl vars p Intlist.empty pvs in
     let cln, _ = flex_closure Neg env lvl vars n Intlist.empty nvs in
     subtype_styp env apxcache clp cln
  | Erigid { names=_; vars; flow } ->
     (* p ⊔ pvs ≤ n ⊓ nvs splits into:
          1. p ≤ n
          2. ∀ pv ∈ pvs, U(pv) ≤ n
          3. ∀ nv ∈ nvs, p ≤ L(nv)
          4. ∀ pv ∈ pvs, nv ∈ nvs. U(pv) ≤ L(nv) OR (pv,nv) ∈ flow
        Algorithm here is to combine (1,3) and (2,4):
          1,3: p ≤ n ⊓ {L(nv) | nv ∈ nvs}
          2,4: ∀pv ∈ pvs, U(pv) ≤ n ⊓ {L(nv) | nv ∈ nvs, (pv,nv) ∉ flow}
        Could equally have chosen to combine differently, or not combine.
        Important to ensure that there are no duplicate checks, so that
        errors are reported only once. *)
     let nbound nvs =
       nvs |> Intlist.to_list |> List.fold_left (fun ty (nv, ()) ->
         join Neg ty vars.(nv).rig_lower) n in
     let errs = subtype_styp env apxcache p (nbound nvs) in
     pvs |> Intlist.to_list |> List.fold_left (fun errs (pv, ()) ->
       let nvs = Intlist.filter (fun nv () -> not (Flow_graph.mem flow pv nv)) nvs in
       subtype_styp env apxcache vars.(pv).rig_upper (nbound nvs) @ errs) errs
  | _ ->
     failwith "expected variables at this env level"

(* extra wf checks *)
let subtype_styp env apxcache p n =
  let r = subtype_styp env apxcache p n in
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  r


(* Give a typ well-formed in ext, approx in env.
   Same as approx_styp *)
let rec approx env lvl pol t =
  wf_env env;
  wf_typ pol env t;
  match t with
  | Tpoly {names; bounds; flow; body} ->
     let (env, _, body) = enter_poly pol env names bounds flow body in
     approx env lvl pol body
  | Tsimple s ->
     approx_styp env (Hashtbl.create 1) lvl pol s
  | Tcons cons ->
     styp_cons pol (map_head pol (approx env lvl) cons)

(* Always Pos <= Neg *)
let rec subtype env p n =
  (* PPrint.(ToChannel.pretty 1. 80 stdout (group (pr_env env ^^ string " ⊢") ^^ break 1 ^^ group (group (pr_typ Pos p) ^^ break 1 ^^ string "≤" ^^ break 1 ^^ group (pr_typ Neg n)) ^^ hardline)); *)
  wf_env env;
  wf_typ Pos env p;
  wf_typ Neg env n;
  match p, n with
  (* FIXME: some sort of coherence check needed. Where? *)
  | p, Tpoly {names; bounds; flow; body} ->
     let env, _, body = enter_poly_neg env names bounds flow body in
     subtype env p body
  | Tpoly {names; bounds; flow; body}, n ->
     let env, _, body = enter_poly_pos env names bounds flow body in
     subtype env body n
  | Tcons s, Tcons t ->
     subtype_cons Pos s t
       (pol_flip (subtype env))

  (* FIXME this is wrong *)
  | (Tsimple _, _) | (_, Tsimple _) ->
     let level = match env with Env_cons { level; _ } -> level | _ -> assert false in
     let p = approx env level Pos p in
     let n = approx env level Neg n in
     subtype_styp env (Hashtbl.create 1) p n

let fresh_flow env l =
  flow_of_flexvar env l (fresh_flexvar env l)

let rec match_styp env (p : styp) (t : unit cons_head) : styp cons_head * conflict_reason list =
  wf_env env;
  wf_styp Pos env p;
  match p with
  | Bound_var _ -> assert false
  | Cons { pol=_; cons } -> cons, []
  | Free_vars { level = lvl; rest = p; vars = vs } ->
     match env_entry_at_level env lvl with
     | Eflexible {vars=fvs;_} ->
        vs |> Intlist.to_list |> List.fold_left (fun (r, errs) (v,()) ->
          let fv = Vector.get fvs v in
          let cons = join_cons Neg fv.neg_match_cache
                       (map_head Neg (fun pol () -> styp_trivial pol) t) in
          let freshen pol t =
            match t with
            | Free_vars { level; vars; rest } when is_trivial pol rest ->
               t, styp_vars (polneg pol) level vars
            | t when is_trivial pol t ->
              let n, p = fresh_flow env lvl in
              (match pol with Neg -> n, p | Pos -> p, n)
            | _ -> assert false in
          let cons = map_head Neg freshen cons in
          let cn = map_head Neg (fun _ t -> fst t) cons in
          let cp = map_head Neg (fun _ t -> snd t) cons in
          fv.neg_match_cache <- cn;
          let errs' =
            subtype_styp env (Hashtbl.create 1)
              (styp_var Pos lvl v)
              (styp_cons Neg cn) in
          join_cons Pos r cp, errs @ errs'
        ) (match_styp env p t)
     | Erigid {names=_; vars; flow=_} ->
        let p = vs |> Intlist.to_list |> List.fold_left (fun r (v,()) ->
          join Pos r vars.(v).rig_upper) p in
        match_styp env p t
     | _ -> intfail "expected variables here"

(* match_type env t⁺ m = t⁺ ≤ m *)
let rec match_type env lvl (p : typ) (t : typ ref cons_head) =
  wf_env env;
  wf_typ Pos env p;
  match p with
  | Tcons cons ->
     subtype_cons Pos cons t (fun pol p r ->
       assert (!r = Tcons (ident pol));
       wf_typ pol env p;
       r := p;
       [])
  | Tpoly {names=_; bounds; flow; body} ->
     (* t is not ∀, so we need to instantiate p *)
     let inst = instantiate_flexible env (Lazy.force lvl) bounds flow in
     let body = map_bound_typ Esort_flexible 0 inst Pos body in
     wf_env env;
     wf_typ Pos env body;
     match_type env lvl body t
  | Tsimple p ->
     let tcons, errs = match_styp env p (map_head Neg (fun _ _ -> ()) t) in
     subtype_cons Pos tcons t (fun pol p r ->
       assert (!r = Tcons (ident pol));
       wf_styp pol env p;
       r := Tsimple p;
       []) @ errs
