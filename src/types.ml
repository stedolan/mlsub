open Tuple_fields
open Typedefs

exception Internal of string
let intfail s = raise (Internal s)
let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

(* join Pos = ⊔, join Neg = ⊓ (meet) *)
let rec join pol (s : styp) (t : styp) =
  assert (s.pol = pol && t.pol = pol);
  match s.body, t.body with
  | Styp s, Styp t ->
     { body = Styp { cons = join_cons pol s.cons t.cons;
                     tyvars = vset_union s.tyvars t.tyvars }; pol }
  | _ -> assert false  (* locally closed *)
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
     let fnames = sf.fnames @
       List.filter (fun k -> not (FieldMap.mem k sf.fields)) tf.fnames in
     let fields = FieldMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | (Some _ as x), None | None, (Some _ as x) ->
          same := false;
          x
       | None, None -> None) sf.fields tf.fields in
     assert (List.length fnames = FieldMap.cardinal fields);
     begin match sf.fopen, tf.fopen, !same with
     | `Open, `Open, _ ->
        Some {fnames; fields; fopen = `Open}
     | _, _, true ->
        (* Not both open, but same fields *)
        Some {fnames; fields; fopen = `Closed}
     | _, _, false ->
        (* Neither both open nor same fields *)
        None
     end
  | Pos ->
     (* upper bound - intersection of fields *)
     let same = ref true in
     let fnames = List.filter (fun k -> FieldMap.mem k tf.fields) sf.fnames in
     let fields = FieldMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | None, Some _ | Some _, None ->
          same := false;
          None
       | _ -> None) sf.fields tf.fields in
     assert (List.length fnames = FieldMap.cardinal fields);
     begin match sf.fopen, tf.fopen, !same with
     | `Closed, `Closed, true ->
        Some {fnames; fields; fopen = `Closed }
     | _, _, _ ->
        Some {fnames; fields; fopen = `Open }
     end

type conflict_reason =
  | Incompatible
  | Missing of field_name
  | Extra of [`Fields|`Named of field_name]

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


(*
(* Hoist a flexible variable to a wider environment *)
let rec hoist_flexible env v =
  assert_env_prefix env v.env;
  wf_env v.env;
  if env == v.env then v
  else match v.hoisted with
  | Some v' when Env_level.extends env.level v'.env.level ->
     hoist_flexible env v'
  | vh ->
     (* Write the hoisted field _before_ approxing bounds,
        so that we terminate when hoisting a var with recursive bounds. *)
     let v' = fresh_flexible env in
     v'.hoisted <- vh;
     v.hoisted <- Some v';
     wf_env v.env;
     let ty_pos = styp_of_vset Pos (vset_of_flexvar v') in
     let ty_neg = styp_of_vset Neg (vset_of_flexvar v') in
     (* I. approx bounds *)
     let bpos = approx_styp env v.env Pos v.pos in
     let bneg = approx_styp env v.env Neg v.neg in
     wf_env v.env;
     v'.pos <- bpos;
     v'.neg <- bneg;
     (* To maintain the ε-invariant, we may need to add other ε-edges *)
     let _, posv = styp_uncons env Flexible bpos in
     let _, negv = styp_uncons env Flexible bneg in
     posv |> List.iter (fun vi ->
       let vother = env_flexvar env vi in
       vother.neg <- join Neg vother.neg ty_neg);
     negv |> List.iter (fun vi ->
       let vother = env_flexvar env vi in
       vother.pos <- join Pos vother.pos ty_pos);
     wf_env v.env;
     (* II. add variable constraints *)
     v.pos <- join Pos v.pos ty_pos;
     v.neg <- join Neg v.neg ty_neg;
     wf_env v.env;
     v'

and approx_vset env pol = function
  | VSnil -> styp_of_vset pol VSnil
  | VScons { env = env'; _ } as vs
       when env_level env' <= env_level env ->
     (* already valid in env *)
     styp_of_vset pol vs
  | VScons { env = env'; sort; vars; rest } ->
     assert_env_prefix env env';
     let acc = approx_vset env pol rest in
     match sort with
     | Rigid ->
        failwith "rigid approx unimplemented"
     | Flexible ->
        List.fold_left (fun acc i ->
          let v = hoist_flexible env (env_flexvar env' i) in
          join pol acc (styp_of_vset pol (vset_of_flexvar v)))
          acc vars

(* Given a styp well-formed in ext,
   find the best approximation well-formed in the shorter environment env.

   This may require hoisting some flexible variables from ext to env.

   Pos types are approximated from above and Neg types from below. *)
and approx_styp env ext pol' ({ tyvars; cons; pol } as orig) =
  assert_env_prefix env ext;
  wf_env ext;
  wf_styp pol' ext orig;
  assert (pol = pol');
  if env_equal env ext then orig
  else
    let cons = map_head pol (approx_styp env ext) cons in
    let ty = join pol { pol; cons; tyvars = VSnil } (approx_vset env pol tyvars) in
    wf_env ext;
    wf_styp pol env ty;
    ty
*)


let fresh_flexvar env (lvl, mark) =
  let fv = env_flexvars env lvl mark in
  Vector.push fv { name = None;
                   pos = cons_styp Pos vsnil (ident Pos);
                   neg = cons_styp Neg vsnil (ident Neg);
                   pos_match_cache = ident Pos;
                   neg_match_cache = ident Neg }

let vset_of_flexvar (lvl, mark) v =
  Intlist.singleton lvl (mark, Intlist.singleton v ())

let flow_of_flexvar _env l v =
  let vset = vset_of_flexvar l v in
  (cons_styp Neg vset (ident Neg)),
  (cons_styp Pos vset (ident Pos))


(* maps (l1, v, pol, l2) -> (_, v') when (l2,v') approximates (l1,v) w/ polarity pol *)
type apxcache = (Env_level.t * int * polarity * Env_level.t, Env_marker.t * int) Hashtbl.t

(* Given a styp well-formed in ext,
   find the best approximation well-formed in the shorter environment env.

   This may require hoisting some flexible variables from ext to env.

   Pos types are approximated from above and Neg types from below. *)
let rec approx_styp env apxcache lvl mark pol ty =
  wf_styp pol env ty;
  if env.level = lvl then ty
  else match styp_max_var_level ty with
  | Some (lvl', mark') when lvl' > lvl ->
     (* needs approx *)
     let rest, vars = styp_unconsv lvl' mark' ty in
     vars |> Intlist.to_list |> List.fold_left (fun ty (v, ()) ->
       join pol ty (approx_styp_var env apxcache lvl mark pol lvl' mark' v))
       (approx_styp env apxcache lvl mark pol rest)
  | _ ->
     (* just approx cons, vars are fine *)
     match ty with
     | { pol = pol'; body = Styp { tyvars; cons } } ->
        assert (pol = pol');
        { pol; body = Styp { tyvars; cons = map_head pol (approx_styp env apxcache lvl mark) cons } }
     | _ -> assert false (* locally closed *)

and approx_styp_var env apxcache lvl mark pol lvl' mark' v' =
  (* approximate the variable v at (lvl', mark') to (lvl, mark) *)
  assert (lvl < lvl');
  match env_entry_at_level env lvl' mark' with
  | Eflexible {vars=flexvars'; _} ->
     begin match Hashtbl.find apxcache (lvl', v', pol, lvl) with
     | (mark'', v) ->
        Env_marker.assert_equal mark mark'';
        cons_styp pol (vset_of_flexvar (lvl, mark) v) (ident pol)
     | exception Not_found ->
        let v = fresh_flexvar env (lvl, mark) in
        Hashtbl.add apxcache (lvl', v', pol, lvl) (mark, v);
        let fv = Vector.get (env_flexvars env lvl mark) v in
        let fv' = Vector.get flexvars' v' in
        let v = vset_of_flexvar (lvl, mark) v in
        begin match pol with
        | Pos ->
           (* v >= v' *)
           let apx = approx_styp env apxcache lvl mark Pos fv'.pos in
           fv.pos <- join Pos fv.pos apx;
           (* preserve ε-inv *)
           Intlist.iter (snd (styp_unconsv lvl mark apx)) (fun ev () ->
             let efv = Vector.get (env_flexvars env lvl mark) ev in
             efv.neg <- join Neg efv.neg (cons_styp Neg v (ident Neg)));
           fv'.neg <- join Neg fv'.neg (cons_styp Neg v (ident Neg))
        | Neg ->
           (* v <= v' *)
           let apx = approx_styp env apxcache lvl mark Neg fv'.neg in
           fv.neg <- join Neg fv.neg apx;
           (* preserve ε-inv *)
           Intlist.iter (snd (styp_unconsv lvl mark apx)) (fun ev () ->
             let efv = Vector.get (env_flexvars env lvl mark) ev in
             efv.pos <- join Pos efv.pos (cons_styp Pos v (ident Pos)));
           fv'.pos <- join Pos fv'.pos (cons_styp Pos v (ident Pos));
        end;
        cons_styp pol v (ident pol)
     end
  | Erigid {names=_; vars; flow=_} ->
     let rv = vars.(v') in
     let bound = match pol with Pos -> rv.rig_upper | Neg -> rv.rig_lower in
     approx_styp env apxcache lvl mark pol bound
  | _ ->
     failwith "expected variables at this env level"

let approx_styp env apxcache lvl mark pol ty =
  let res = approx_styp env apxcache lvl mark pol ty in
  wf_styp pol (env_at_level env lvl mark) res;
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


let rec flex_closure pol env lvl mark flexvars (t : styp) vseen vnew =
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
    let t, vnext = styp_unconsv lvl mark t in
    flex_closure pol env lvl mark flexvars t vseen (Intlist.remove vnext vseen)
  end
  
(* The termination condition here is extremely tricky, if it's even true *)

(* env ⊢ p ≤ n *)
let rec subtype_styp env (apxcache : apxcache) (p : styp) (n : styp) =
  (* PPrint.(ToChannel.pretty 1. 80 stdout (hardline ^^ group (group (pr_env env ^^ string " ⊢") ^^ break 1 ^^ group (group (pr_styp Pos p) ^^ break 1 ^^ string "≤" ^^ break 1 ^^ group (pr_styp Neg n))) ^^ hardline)); *)
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  let max_var_level =
    match styp_max_var_level p, styp_max_var_level n with
    | None, None -> None
    | (Some _ as x), None | None, (Some _ as x) -> x
    | (Some (lp, _) as p), (Some (ln, _) as n) ->
       if lp > ln then p else n in
  let errs = match max_var_level with
  | None ->
     (match p, n with
     | { body = Styp { cons = p; _ }; _ }, { body = Styp { cons = n; _ }; _ } ->
        subtype_cons Pos p n (pol_flip (subtype_styp env apxcache))
     | _ -> assert false)
  | Some (lvl, mark) ->
     let pcons, pvars = styp_unconsv lvl mark p in
     let ncons, nvars = styp_unconsv lvl mark n in
     subtype_styp_vars env apxcache lvl mark p n pcons ncons pvars nvars in
  (* Printf.printf "%d\n%!" (List.length errs); *)
  errs

(* env ⊢ p ⊔ pv ≤ n ⊓ nv, where pv, nv same level, above anything else in p,n *)
and subtype_styp_vars env apxcache lvl mark orig_p orig_n (p : styp) (n : styp) pvs nvs =
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  match env_entry_at_level env lvl mark with
  | Eflexible {vars;_} ->
     (* FIXME: avoid some calls to approx_styp for constraints that already hold! *)
     Intlist.iter pvs (fun pv () ->
       let pv = Vector.get vars pv in
       pv.neg <- join Neg pv.neg (approx_styp env apxcache lvl mark Neg orig_n)
     );
     Intlist.iter nvs (fun nv () ->
       let nv = Vector.get vars nv in
       nv.pos <- join Pos nv.pos (approx_styp env apxcache lvl mark Pos orig_p)
     );
     wf_env env;
     let clp, _ = flex_closure Pos env lvl mark vars p Intlist.empty pvs in
     let cln, _ = flex_closure Neg env lvl mark vars n Intlist.empty nvs in
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
let rec approx env lvl mark pol t =
  wf_env env;
  wf_typ pol env t;
  match t with
  | Tpoly {names; bounds; flow; body} ->
     let (env, body) = enter_poly pol env names bounds flow body in
     approx env lvl mark pol body
  | Tsimple s ->
     approx_styp env (Hashtbl.create 1) lvl mark pol s
  | Tcons cons ->
     cons_styp pol vsnil (map_head pol (approx env lvl mark) cons)

(* Always Pos <= Neg *)
let rec subtype env p n =
  (* PPrint.(ToChannel.pretty 1. 80 stdout (group (pr_env env ^^ string " ⊢") ^^ break 1 ^^ group (group (pr_typ Pos p) ^^ break 1 ^^ string "≤" ^^ break 1 ^^ group (pr_typ Neg n)) ^^ hardline)); *)
  wf_env env;
  wf_typ Pos env p;
  wf_typ Neg env n;
  match p, n with
  (* FIXME: some sort of coherence check needed. Where? *)
  | p, Tpoly {names; bounds; flow; body} ->
     let env, body = enter_poly_neg env names bounds flow body in
     subtype env p body
  | Tpoly {names; bounds; flow; body}, n ->
     let env, body = enter_poly_pos env names bounds flow body in
     subtype env body n
  | Tcons s, Tcons t ->
     subtype_cons Pos s t
       (pol_flip (subtype env))
  | (Tsimple _, _) | (_, Tsimple _) ->
     let p = approx env env.level env.marker Pos p in
     let n = approx env env.level env.marker Neg n in
     subtype_styp env (Hashtbl.create 1) p n

let fresh_flow env l =
  flow_of_flexvar env l (fresh_flexvar env l)

let rec match_styp env (p : styp) (t : unit cons_head) : styp cons_head * conflict_reason list =
  wf_env env;
  wf_styp Pos env p;
  match styp_max_var_level p with
  | None -> (match p.body with Styp { cons; _ } -> cons, [] | _ -> assert false)
  | Some (lvl, mark) ->
     let p, vs = styp_unconsv lvl mark p in
     match env_entry_at_level env lvl mark with
     | Eflexible {vars=fvs;_} ->
        vs |> Intlist.to_list |> List.fold_left (fun (r, errs) (v,()) ->
          let fv = Vector.get fvs v in
          let cons = join_cons Neg fv.neg_match_cache
                       (map_head Neg (fun pol () -> cons_styp pol vsnil (ident pol)) t) in
          let freshen pol t =
            if Intlist.is_empty (match t.body with Styp s -> s.tyvars | _ -> assert false) then
              let n, p = fresh_flow env (lvl, mark) in
              match pol with Neg -> n, p | Pos -> p, n
            else
              let _lvl', (mark', vs) = Intlist.as_singleton (match t.body with Styp s -> s.tyvars | _ -> assert false) in
              Env_marker.assert_equal mark mark';
              let v, () = Intlist.as_singleton vs in
              t, cons_styp (polneg pol) (vset_of_flexvar (lvl, mark) v) (ident (polneg pol)) in
          let cons = map_head Neg freshen cons in
          let cn = map_head Neg (fun _ t -> fst t) cons in
          let cp = map_head Neg (fun _ t -> snd t) cons in
          fv.neg_match_cache <- cn;
          let errs' =
            subtype_styp env (Hashtbl.create 1)
              (cons_styp Pos (vset_of_flexvar (lvl, mark) v) (ident Pos))
              (cons_styp Neg vsnil cn) in
          join_cons Pos r cp, errs @ errs'
        ) (match_styp env p t)
     | Erigid {names=_; vars; flow=_} ->
        let p = vs |> Intlist.to_list |> List.fold_left (fun r (v,()) ->
          join Pos r vars.(v).rig_upper) p in
        match_styp env p t
     | _ -> intfail "expected variables here"

(* match_type env t⁺ m = t⁺ ≤ m *)
let rec match_type env (lvl, mark) (p : typ) (t : typ ref cons_head) =
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
     let body = instantiate_flexible env lvl mark bounds flow body in
     wf_env env;
     wf_typ Pos env body;
     match_type env (lvl, mark) body t
  | Tsimple p ->
     let tcons, errs = match_styp env p (map_head Neg (fun _ _ -> ()) t) in
     subtype_cons Pos tcons t (fun pol p r ->
       assert (!r = Tcons (ident pol));
       wf_styp pol env p;
       r := Tsimple p;
       []) @ errs
