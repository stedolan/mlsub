open Tuple_fields
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
       List.filter (fun k -> not (SymMap.mem k sf.fnamed)) tf.fnames in
     let fnamed = SymMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | (Some _ as x), None | None, (Some _ as x) ->
          same := false;
          x
       | None, None -> None) sf.fnamed tf.fnamed in
     assert (List.length fnames = SymMap.cardinal fnamed);
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
     let fnames = List.filter (fun k -> SymMap.mem k tf.fnamed) sf.fnames in
     let fnamed = SymMap.merge (fun _ s t ->
       match s, t with
       | Some s, Some t -> Some (join pol s t)
       | None, Some _ | Some _, None ->
          same := false;
          None
       | _ -> None) sf.fnamed tf.fnamed in
     assert (List.length fnames = SymMap.cardinal fnamed);
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
         match SymMap.find k bf.fnamed with
         | exception Not_found -> Extra (`Named k) :: acc
         | _ -> acc) af.fnames extra_errs
    | Neg, `Closed, _ ->
       (* check dom b ⊆ dom a *)
       let extra_errs =
         if List.length bf.fpos > List.length af.fpos then
           Extra `Positional :: extra_errs else extra_errs in
       List.fold_right (fun k acc ->
         match SymMap.find k af.fnamed with
         | exception Not_found -> Extra (`Named k) :: acc
         | _ -> acc) bf.fnames extra_errs
    | _ -> extra_errs in

  let rec subtype_pos i aps bps acc = match aps, bps, pol with
    | [], [], _ -> acc
    | _, [], Pos | [], _, Neg -> acc (* extra fields handled above *)
    | [], _, Pos | _, [], Neg -> Missing `Positional :: acc
    | ap :: aps, bp :: bps, pol ->
       f pol (Field_positional i) ap bp @ subtype_pos (i+1) aps bps acc in
  let errs = subtype_pos 0 af.fpos bf.fpos extra_errs in
  match pol with
  | Pos ->
    SymMap.fold (fun k b acc ->
      match SymMap.find k af.fnamed with
      | exception Not_found -> Missing (`Named k) :: acc
      | a -> f pol (Field_named k) a b @ acc) bf.fnamed errs
  | Neg ->
     SymMap.fold (fun k a acc ->
      match SymMap.find k bf.fnamed with
      | exception Not_found -> Missing (`Named k) :: acc
      | b -> f pol (Field_named k) a b @ acc) af.fnamed errs

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


(* Compute epsilon-closure of a type *)
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



(* Hoist a flexible variable to a wider environment *)
let rec hoist_flexible env v =
  assert_env_prefix env v.env;
  wf_env v.env;
  if env == v.env then v
  else match v.hoisted with
  | Some v' when env_level env <= env_level v'.env ->
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


(*
  Given some variables in environment venv ≤ env,
  flex_closure returns the join of the bounds of their ε-closures.
  The result will not have flexible toplevel variables beyond level venv.
  (assuming the same is true for acc)
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
      go (join pol t acc) newvs end) acc vars in
  let res = go acc vars in
  wf_styp pol env res;
  assert (snd (styp_uncons venv Flexible res) = []);
  res


let pol_flip f pol a b =
  match pol with Pos -> f a b | Neg -> f b a

(* FIXME: this factoring doesn't seem the simplest.
   Inline subtype_styp_vars? *)
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
     (* FIXME: wtf? *)
     let vsort = min pv.sort nv.sort in (* i.e. Flex if either is *)
     subtype_styp_vars env p n pv.env vsort
  | VScons pv, VScons nv when
      env_level pv.env > env_level nv.env ->
     subtype_styp_vars env p n pv.env pv.sort
  | VScons pv, VScons nv ->
     assert (env_level pv.env < env_level nv.env);
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
     let n_apx = approx_styp venv env Neg n in
     let p_apx = approx_styp venv env Pos p in
     pvs |> List.iter (fun pvi ->
       let v = env_flexvar venv pvi in
       v.neg <- join Neg v.neg n_apx);
     nvs |> List.iter (fun nvi ->
       let v = env_flexvar venv nvi in
       v.pos <- join Pos v.pos p_apx);
     subtype_styp env
       (flex_closure Pos env prest venv pvs)
       (flex_closure Neg env nrest venv nvs)
  | Rigid ->
     (* this is a load of bollocks *)
     assert false

let subtype_styp env p n =
  let r = subtype_styp env p n in
  wf_env env;
  wf_styp Pos env p;
  wf_styp Neg env n;
  r



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

(* match_type env t⁺ m = t⁺ ≤ m *)
let rec match_type env (p : typ) (t : typ ref cons_head) =
  wf_env env;
  wf_typ Pos env p;
  match p with
  | Tcons cons ->
     subtype_cons Pos cons t (fun pol p r ->
       assert (!r = Tcons (ident pol));
       wf_typ pol env p;
       r := p;
       [])
  | Tpoly_neg _ -> assert false (* can't happen, positive type *)
  | Tpoly_pos (vars, body) ->
     (* t is not ∀, so we need to instantiate p *)
     let vsets = instantiate_flexible env vars in
     wf_env env;
     let body = open_typ Flexible vsets 0 Pos body in
     match_type env body t
  | Tsimple (Tstyp_bound _) ->
     (* bound variable escaped, something's wrong *)
     assert false
  | Tsimple (Tstyp_simple p) ->
     match p.tyvars with
     | VSnil ->
        (* Optimisation in the case of no flow *)
        subtype_cons Pos p.cons t (fun pol p r ->
          assert (!r = Tcons (ident pol));
          wf_styp pol env p;
          r := Tsimple (Tstyp_simple p);
          [])
     | _ ->
        let freshen pol r =
          assert (!r = Tcons (ident (polneg pol)));
          let v = vset_of_flexvar (fresh_flexible env) in
          let st = (cons_styp (polneg pol) v (ident (polneg pol))) in
          (* FIXME: is this the right pol? *)
          wf_env env;
          wf_styp (polneg pol) env st;
          r := (Tsimple (Tstyp_simple st));
          cons_styp pol v (ident pol) in
        let t = cons_styp Neg VSnil (map_head Neg freshen t) in
        let res = subtype_styp env p t in
        wf_env env;
        wf_styp Pos env p;
        res

let fresh_flow env =
  let v = vset_of_flexvar (fresh_flexible env) in
  Tsimple (Tstyp_simple (cons_styp Neg v (ident Neg))),
  Tsimple (Tstyp_simple (cons_styp Pos v (ident Pos)))

