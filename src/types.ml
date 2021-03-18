open Tuple_fields
open Typedefs

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)

type conflict_reason =
  | Incompatible of string * string
  | Missing of field_name
  | Extra of [`Fields|`Named of field_name]

(*
 * Subtyping, meet and join on constructed types
 *)

let subtype_cons_fields ~error f af bf =
  if bf.fopen = `Closed then begin
    if af.fopen = `Open then error (Extra `Fields);
    (* check dom a ⊆ dom b *)
    List.iter (fun k ->
      match FieldMap.find k bf.fields with
      | exception Not_found -> error (Extra (`Named k))
      | _ -> ()) af.fnames
  end;
  FieldMap.iter (fun k b ->
    match FieldMap.find k af.fields with
    | exception Not_found -> error (Missing k)
    | a -> f a b) bf.fields

let subtype_cons ~error ~pos ~neg a b =
  match a, b with
  | Bot, _ | _, Top -> ()
  | Bool, Bool -> ()
  | Int, Int -> ()
  | String, String -> ()
  | Func (args, res), Func (args', res') ->
     subtype_cons_fields ~error neg args' args; pos res res'
  | Record fs, Record fs' ->
     subtype_cons_fields ~error pos fs fs'
  | a,b ->
     let msg = function
       | Bot -> "bot"
       | Bool -> "bool"
       | Int -> "int"
       | String -> "string"
       | Func _ -> "func"
       | Record _ -> "record"
       | Top -> "top" in
     error (Incompatible (msg a, msg b))

(* NB: nleft/nright/nboth = contravariant
   Since meet is used on negative types, these will be *positive* *)
let meet_cons
  ~nleft ~nright ~nboth
  ~pleft ~pright ~pboth
  a b =
  match a, b with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | c, Top -> map_head nleft pleft c
  | Top, c' -> map_head nright pright c'
  | Bool, Bool -> Bool
  | Int, Int -> Int
  | String, String -> String
  | (Bool|Int|String), _ | _, (Bool|Int|String) -> Bot
  | Record _, Func _ | Func _, Record _ -> Bot
  | Record c, Record c' ->
     begin match Tuple_fields.union ~left:pleft ~right:pright ~both:pboth c c' with
     | Some r -> Record r
     | None -> Bot
     end
  | Func (args, res), Func (args', res') ->
     (* FIXME: fail here rather than assuming variadic functions?
        Could/should enforce that functions are always `Closed *)
     let args = Tuple_fields.inter ~both:nboth args args' in
     Func (args, pboth res res')

let join_cons
  ~nleft ~nright ~nboth
  ~pleft ~pright ~pboth
  a b =
  match a, b with
  | Top, _ | _, Top -> Top
  | c, Bot -> map_head nleft pleft c
  | Bot, c' -> map_head nright pright c'
  | Bool, Bool -> Bool
  | Int, Int -> Int
  | String, String -> String
  | (Bool|Int|String), _ | _, (Bool|Int|String) -> Top
  | Record _, Func _ | Func _, Record _ -> Top
  | Record c, Record c' ->
     Record (Tuple_fields.inter ~both:pboth c c')
  | Func (args, res), Func (args', res') ->
     begin match Tuple_fields.union ~left:nleft ~right:nright ~both:nboth args args' with
     | Some r -> Func (r, pboth res res')
     | None -> Top
     end

let contains_rigvar (v : rigvar) vs =
  List.exists (fun rv -> rv = v) vs

let join_rigvars c vs =
  let vs = List.filter (fun v -> not (contains_rigvar v c.rigvars)) vs in
  { c with rigvars = c.rigvars @ vs }

(* There are two ways to represent a constraint α ≤ β between two flexible variables.
   (I). Make the upper bound of α be UBvar β. (Ensure also that LB(β) contains LB(α))
   (II). Make the lower bound of β contain α. (Ensure also that UB(α) contains UB(β)) *)


let noerror _ = failwith "subtyping error should not be possible here!"

let bottom = {ctor={cons=Bot;rigvars=[]};flexvars=[]}

let flexlb_fv fv = { ctor = { cons = Bot; rigvars = [] }; flexvars = [fv] }


(*
 * Core subtyping functions
 *)


let fresh_flexvar level = fresh_flexvar_gen level UBnone

(* equivalent to making a fresh var and constraining <= fv
   fv must be at or below lvl *)
let fresh_below_var lvl fv =
  assert (Env_level.extends fv.level lvl);
  fresh_flexvar_gen lvl (UBvar fv)

let rec duplicate_contravariant_lower lvl t =
  { t with ctor = map_ctor_rig (fresh_below_var lvl) (duplicate_contravariant_lower lvl) t.ctor }
let duplicate_covariant_upper lvl c =
  map_ctor_rig (duplicate_contravariant_lower lvl) (fresh_below_var lvl) c

(* equivalent to making a fresh var and constraining <= cn
   cn must be wf at lvl. FIXME: check this thoroughly *)
let fresh_below_cons lvl {cons;rigvars} =
  List.iter (fun (rv : rigvar) -> assert (Env_level.extends rv.level lvl)) rigvars;
  let rigvars = List.sort_uniq compare_rigvar rigvars in (* FIXME: hideous *)
  (* need to freshen covariant parts of cons to preserve matchability. *)
  let ctor = duplicate_covariant_upper lvl {cons; rigvars} in
  fresh_flexvar_gen lvl (UBcons [ctor])


(* add some flexvars to a join.
   does not check levels, so level of resulting join may increase *)
let join_flexvars lower vs =
  if lower.ctor.cons = Top then lower
  else
    match List.filter (fun v -> not (List.memq v lower.flexvars)) vs with
    | [] -> lower
    | vs -> { lower with flexvars = lower.flexvars @ vs }


(* Convert a flexvar's upper bound(s) to UBcons form. May decrease levels. *)
let rec flex_cons_upper ~changes env (fv : flexvar) : (flex_lower_bound, flexvar) ctor_ty list =
  match fv.upper with
  | UBcons c -> c
  | UBnone ->
     (* FIXME: should be [], but this hits more nasty cases in tests for now *)
     assert (fv.lower = { ctor = { cons = Bot; rigvars = [] } ; flexvars = [] });
     let triv = [{cons=Top; rigvars=[]}] in
     fv_set_upper ~changes fv (UBcons triv);
     triv
  | UBvar v ->
     assert (fv.lower = { ctor = { cons = Bot; rigvars = [] } ; flexvars = [] });
     assert (Env_level.extends v.level fv.level);
     let upper = flex_cons_upper ~changes env v in (* NB: may hoist v! *)
     if not (Env_level.equal v.level fv.level) then begin
       (* Hoist fv. Bounds known trivial, so no work needed there *)
       fv_set_level ~changes fv v.level
     end;
     (* ~changes: don't really care, already logging fv *)
     fv_set_lower ~changes v (join_flexvars v.lower [fv]); (* wf: levels equal *)
     (* To preserve matchability, need to freshen the covariant variables in pv.upper. *)
     (* No hoisting needed since we're at the same level as v *)
     let upper = List.map (duplicate_covariant_upper fv.level) upper in
     fv_set_upper ~changes fv (UBcons upper);
     upper

(* Check whether a flex-flex constraint α ≤ β is already present.
   NB: walks UBvar upper bounds, but does not walk lower bounds.
       Upper bounds are walked to avoid creating UBvar cycles.
       Lower bounds are not walked to allow expand to redundantly fill them in. *)
let rec flex_flex_already pv nv =
  pv == nv ||
  List.memq pv nv.lower.flexvars ||
  match pv.upper with
  | UBvar pv' -> flex_flex_already pv' nv
  | _ -> false


let rec subtype_t_var ~error ~changes env (p : flex_lower_bound) (nv : flexvar) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_flex ~error ~changes env pv nv);
  subtype_cons_flex ~error ~changes env p.ctor nv

and subtype_t_cons ~error ~changes env (p : flex_lower_bound) (cn : (flex_lower_bound, flexvar) ctor_ty) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_cons ~error ~changes env pv cn);
  subtype_ctor_rig ~error ~changes env p.ctor cn

and subtype_ctor_rig ~error ~changes env cp cn =
  cp.rigvars |> List.iter (fun pv ->
    if contains_rigvar pv cn.rigvars then ()
    else subtype_ctor_rig ~error ~changes env (env_rigid_bound env pv) cn);
  subtype_cons ~error
    ~neg:(subtype_t_var ~error ~changes env)
    ~pos:(subtype_t_var ~error ~changes env) cp.cons cn.cons;
  ()

and subtype_flex_flex ~error ~changes env (pv : flexvar) (nv : flexvar) =
  if flex_flex_already pv nv then ()
  else match pv.upper with
  | UBnone when
       Env_level.extends nv.level pv.level
       && not (flex_flex_already nv pv) (* avoid creating cycles *)
     ->
     fv_set_upper ~changes pv (UBvar nv);
     subtype_t_var ~error ~changes env pv.lower nv
  | _ ->
     (* FIXME rectypes support affected by ordering here *)
     let upper = flex_cons_upper ~changes env nv in
     fv_set_lower ~changes nv (join_flexvars nv.lower [pv]);
     (* FIXME: maybe flex_cons_upper should return level? TOCTOU otherwise *)
     (* FIXME: ordering of side-effects here *)
     hoist_flex ~error ~changes env nv.level pv;
     assert (Env_level.extends pv.level nv.level);
     upper |> List.iter (fun u -> subtype_flex_cons ~error ~changes env pv u);
     ()

and subtype_flex_cons ~error ~changes env pv cn =
  let cp = ensure_upper_matches ~error ~changes env pv (map_ctor_rig id ignore cn) in
  subtype_cons ~error
    ~neg:(fun _ () -> () (* already done in ensure_upper_matches *))
    ~pos:(subtype_flex_flex ~error ~changes env)
    cp cn.cons;
  ()

(* Ensure every rigvar appearing in a flexvar's lower bounds also
   appears in its upper bounds.
     rv <= a <= C implies rv <= a <= C | rv since rv <= C is C = C | rv *)
and ensure_rigvars_present ~changes env (fv : flexvar) =
  match fv.lower.ctor.rigvars with
  | [] -> ()
  | rvlow ->
     let cbs = flex_cons_upper ~changes env fv in
     let rv_present, rv_absent = cbs |> List.partition (fun {cons=_;rigvars} ->
       rvlow |> List.for_all (fun rv -> List.exists (equal_rigvar rv) rigvars)) in
     match rv_absent with
     | [] -> ()
     | rv_absent ->
        fv_set_upper ~changes fv (UBcons rv_present);
        rv_absent |> List.iter (fun cb ->
          let cb = { cb with rigvars = List.sort_uniq compare_rigvar (cb.rigvars @ rvlow) } in
          (* This shouldn't fail because we already have fv <= cb *)
          subtype_flex_cons ~error:noerror ~changes env fv cb)

(* Ensure pv has a UBcons upper bound whose head is below a given ctor.
   Returns the constructed upper bound. *)
and ensure_upper_matches ~error ~changes env (pv : flexvar) (cn : (flex_lower_bound, unit) ctor_ty) : (unit, flexvar) cons_head =
  let cbs = flex_cons_upper ~changes env pv in
  let cnrig =
    cn.rigvars
    |> List.filter (fun (rv : rigvar) -> Env_level.extends rv.level pv.level)
    |> List.sort_uniq compare_rigvar in
  let cbs_match, cbs_rest =
    List.partition (fun cb -> equal_lists equal_rigvar cb.rigvars cnrig) cbs in
  let cb, new_rvset =
    match cbs_match with
    | [] -> Top, true
    | [c] -> c.cons, false
    | _ -> intfail "duplicate bounds with same rigvar set" in
  let cbnew =
    meet_cons
      ~nleft:id
      ~nright:(fun b -> join_lower ~error ~changes env pv.level bottom b) (* FIXME bad hoist fn *)
      ~nboth:(fun a b -> join_lower ~error ~changes env pv.level a b)
      ~pleft:id
      ~pright:(fun _ -> fresh_flexvar pv.level)
      ~pboth:(fun v _ -> v)
      cb cn.cons in
  if not (equal_cons equal_flex_lower_bound equal_flexvar cb cbnew) then begin
    let bound = { cons = cbnew; rigvars = cnrig } in
    fv_set_upper ~changes pv (UBcons (bound :: cbs_rest));
    (* FIXME is this all still wf, despite hoisting? *)
    subtype_t_cons ~error ~changes env pv.lower bound;
    if new_rvset then ensure_rigvars_present ~changes env pv;
  end;
  map_head ignore id cbnew

and subtype_cons_flex ~error ~changes env (cp : (flexvar, flex_lower_bound) ctor_ty) (nv : flexvar) =
  match cp with
  | { cons = Bot; rigvars = [] } ->
     (* avoid even calling flex_cons_upper in the trivial case *)
     ()
  | cp ->
     let bounds = flex_cons_upper ~changes env nv in
     let lower = join_ctor ~error ~changes env nv.level nv.lower cp in
     (* Printf.printf "lower bound of %a: %a --> %a\n" pp_flexvar nv pp_flexlb nv.lower pp_flexlb lower; *)
     if fv_maybe_set_lower ~changes nv lower then begin
       bounds |> List.iter (fun bound ->
         subtype_ctor_rig ~error ~changes env cp bound);
       ensure_rigvars_present ~changes env nv;
     end

and join_ctor ~error ~changes env level lower cp =
  (* lower is already wf at level, cp may not be *)
  let cons =
    join_cons
       ~nleft:id
       ~nright:(fun y ->
         (* Not fresh_below_var, as hoisting may be needed.
            FIXME test this *)
         let v = fresh_flexvar level in subtype_flex_flex ~error:noerror ~changes env v y; v)
       ~nboth:(fun x y -> subtype_flex_flex ~error:noerror ~changes env x y; x)
       ~pleft:id
       (* NB: pright is not id, because we need fresh variables for contravariant parts,
          to preserve matchability *)
       ~pright:(fun x -> join_lower ~error ~changes env level bottom x)
       ~pboth:(fun x y -> join_lower ~error ~changes env level x y)
       lower.ctor.cons cp.cons in
  (* FIXME: Top case of rigvars? check. *)
  List.fold_left (fun c rv ->
    if contains_rigvar rv c.ctor.rigvars then c
    else if Env_level.extends rv.level level then begin
      { c with ctor = { c.ctor with rigvars = c.ctor.rigvars @ [rv] } }
    end else
      join_ctor ~error ~changes env level c (env_rigid_bound env rv))
    { ctor = { cons; rigvars = lower.ctor.rigvars }; flexvars = lower.flexvars} cp.rigvars

and join_lower ~error ~changes env level lower {ctor; flexvars} =
  let ctor = join_ctor ~error ~changes env level lower ctor in
  List.iter (hoist_flex ~error ~changes env level) flexvars;
  let lb = join_flexvars ctor flexvars in
  lb

and hoist_flex ~error ~changes env level v =
  if Env_level.extends v.level level then ()
  else match v.upper with
    | UBnone ->
       fv_set_level ~changes v level
    | UBvar v' when Env_level.extends v'.level level ->
       fv_set_level ~changes v level
    | _ ->
       let cns = flex_cons_upper ~changes env v in
       (* FIXME hoist vs. copy differs slightly for contravariant components.
          Does this matter? *)
       if Env_level.extends v.level level then
         (* flex_cons_upper above actually did the required hoisting, so we're done *)
         ()
       else begin
         fv_set_level ~changes v level;
         (* FIXME hoisting: seems wrong - need to drop some rigvars here? *)
         let cns = List.map (map_ctor_rig (join_lower ~error ~changes env level bottom)
                               (fun v -> hoist_flex ~error ~changes env level v; v)) cns in
         fv_set_upper ~changes v (UBcons cns);
         hoist_lower ~error ~changes env level v.lower;

         cns |> List.iter (fun cn -> subtype_t_cons ~error ~changes:changes env v.lower cn);
         (* FIXME hoisting: recheck *)
       end

and hoist_lower ~error ~changes env level {ctor;flexvars} =
  (* FIXME hoisting: this looks wrong: what about the levels of ctor.rigvars?  *)
  map_ctor_rig (hoist_flex ~error ~changes env level) (hoist_lower ~error ~changes env level) ctor |> ignore;
  List.iter (hoist_flex ~error ~changes env level) flexvars;
  ()


(*
 * Subtyping on typs (polymorphism)
 *)

(* check that a well-formed type is simple (i.e does not contain a forall) *)
let rec check_simple = function
  | Tsimple _ | Tvar _ -> true
  | Tvjoin _ ->
     (* Anything under the join must be simple by wf-ness *)
     true
  | Tcons c ->
     (* FIXME: a fold would be nicer, surely? *)
     equal_cons (=) (=)
       (map_head (fun _ -> true) (fun _ -> true) c)
       (map_head check_simple check_simple c)
  | Tpoly _ -> false

(* argument must be a simple locally closed type well-formed at lvl *)
let rec simple_ptyp lvl : ptyp -> flex_lower_bound = function
  | Tsimple t -> t
  | Tcons cp ->
     let cons = map_head (simple_ntyp_var lvl) (simple_ptyp lvl) cp in
     { ctor = { cons; rigvars = [] } ; flexvars = [] }
  | Tpoly _ -> intfail "simple_ptyp: Tpoly is not simple"
  | Tvjoin (_, Vbound _) | Tvar (Vbound _) -> intfail "simple_ptyp: not locally closed"
  | Tvar (Vflex fv) ->
     assert (Env_level.extends fv.level lvl);
     { ctor = {cons=Bot;rigvars=[]}; flexvars = [fv] }
  | Tvar (Vrigid rv) ->
     assert (Env_level.extends rv.level lvl);
     { ctor = {cons=Bot; rigvars=[rv]}; flexvars = [] }
  | Tvjoin (t, Vflex fv) ->
     assert (Env_level.extends fv.level lvl);
     join_flexvars (simple_ptyp lvl t) [fv]
  | Tvjoin (t, Vrigid rv) ->
     assert (Env_level.extends rv.level lvl);
     let {ctor={cons;rigvars};flexvars} = simple_ptyp lvl t in
     {ctor={cons;rigvars=if contains_rigvar rv rigvars then rigvars else rigvars@[rv]};flexvars}

(* FIXME: styp_neg isn't really the right type here *)
and simple_ntyp lvl : ntyp -> styp_neg = function
  | Tsimple t -> UBvar t
  | Tcons Top -> UBnone
  | Tcons cn ->
     UBcons [{cons = map_head (simple_ptyp lvl) (simple_ntyp_var lvl) cn; rigvars=[]}]
  | Tpoly _ -> intfail "simple_ntyp: Tpoly is not simple"
  | Tvjoin (_, Vbound _) | Tvar (Vbound _) -> intfail "simple_ntyp: not locally closed"
  | Tvar (Vflex fv) ->
     assert (Env_level.extends fv.level lvl);
     UBvar fv
  | Tvar (Vrigid rv) ->
     assert (Env_level.extends rv.level lvl);
     UBcons [{cons=Bot; rigvars=[rv]}]
  | Tvjoin (_, Vflex _) -> intfail "simple_ntyp: negative join"
  | Tvjoin (t, Vrigid rv) ->
     assert (Env_level.extends rv.level lvl);
     match simple_ntyp rv.level t with
     | UBnone -> UBnone
     | UBvar _ -> intfail "simple_ntyp: rigid/flex negative join"
     | UBcons [{cons;rigvars}] ->
        let rigvars = if contains_rigvar rv rigvars then rigvars else rv::rigvars in
        UBcons [{cons;rigvars}]
     | UBcons _ -> assert false (* FIXME ugly *)

and simple_ntyp_var lvl (t : ntyp) : flexvar =
  match simple_ntyp lvl t with
  | UBnone -> fresh_flexvar lvl
  | UBvar v -> v
  | UBcons [cn] -> fresh_below_cons lvl cn
  | UBcons _ -> assert false (* FIXME ugly *)

let simple_ntyp_bound lvl t =
  match simple_ntyp lvl t with
  | UBnone -> { cons = Top; rigvars = [] }
  | UBcons [c] -> c
  | UBvar _ -> intfail "simple_ntyp_bound: flexvars present in bound"
  | UBcons _ -> assert false (* FIXME ugly *)

let instantiate_flex env vars body =
  let level = env_level env in
  let fvars = IArray.map (fun _ -> fresh_flexvar level) vars in
  IArray.iter2 (fun fv (_, b) ->
    (* FIXME: use fresh_below? *)
    let b = simple_ntyp_bound (env_level env) (open_typ_flex fvars b) in
    subtype_t_cons ~error:noerror ~changes:(ref []) env (flexlb_fv fv) b
  ) fvars vars;
  open_typ_flex fvars body

(* arg must be locally closed, not necessarily simple *)
let rec approx_ptyp env : ptyp -> flex_lower_bound = function
  | Tcons cp ->
     let cons = map_head (approx_ntyp_var env) (approx_ptyp env) cp in
     { ctor = { cons; rigvars = [] }; flexvars = [] }
  | (Tvar _ | Tvjoin _ | Tsimple _) as t -> simple_ptyp (env_level env) t
  | Tpoly {vars;body} ->
     let body = instantiate_flex env vars body in
     approx_ptyp env body


(* FIXME hoisting below here *)
and approx_ntyp env : ntyp -> styp_neg = function
  | Tcons cn ->
     let cons = map_head (approx_ptyp env) (approx_ntyp_var env) cn in
     UBcons [{cons;rigvars=[]}]
  | (Tvar _ | Tvjoin _ | Tsimple _) as t ->
     simple_ntyp (env_level env) t
  | Tpoly {vars; body} ->
     (* Negative var occurrences should be replaced with their upper
        bounds, positive ones should be deleted. *)
     let bounds = Array.make (IArray.length vars) None in
     let neg rest v =
       (match rest with Some _ -> intfail "contravariant join" | None -> ());
       match bounds.(v) with
       | None -> intfail "recursive rigid bound"
       | Some t -> Tsimple t in
     let pos rest _v =
       match rest with
       | None -> Tcons Bot
       | Some t -> t in
     vars |> IArray.iteri (fun i (_, b) ->
       let b = open_typ ~neg:pos ~pos:neg 0 b in
       let b = approx_ptyp env b in
       bounds.(i) <- Some b);
     let body = open_typ ~neg ~pos 0 body in
     approx_ntyp env body

and approx_ntyp_var env (n : ntyp) : flexvar =
  match approx_ntyp env n with
  | UBnone -> fresh_flexvar (env_level env)
  | UBvar v -> v
  | UBcons [cons] ->
     let fv = fresh_flexvar (env_level env) in
     subtype_flex_cons ~error:noerror ~changes:(ref []) env fv cons;
     fv
  | UBcons _ -> assert false (* FIXME ugly *)


let simple_ptyp_bound lvl t =
  match simple_ptyp lvl t with
  | { ctor; flexvars = [] } -> ctor
  | _ -> intfail "simple_ptyp_bound: flexvars present in bound"



(* FIXME: not ideal, probably copies too many vars *)
let join_simple env lvl p q =
  let r = bottom in
  (* FIXME: maybe this can fail if lvl != env_level? *)
  let r = join_lower ~error:noerror ~changes:(ref []) env lvl r p in
  let r = join_lower ~error:noerror ~changes:(ref []) env lvl r q in
  r

(* FIXME: rank1 joins maybe?
   FIXME: keep types as Tcons if possible? Better inference. Can this matter? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  Tsimple (join_simple env (env_level env) (approx_ptyp env p) (approx_ptyp env q))

let rec match_simple_typ ~error ~changes env lvl (p : flex_lower_bound) (head : (flex_lower_bound, flex_lower_bound ref) cons_head) =
  let {ctor = {cons; rigvars}; flexvars} = p in
  subtype_cons ~error cons head
    ~neg:(subtype_t_var ~error ~changes env)
    ~pos:(fun p r -> r := join_lower ~error ~changes env lvl !r p);
  rigvars |> List.iter (fun rv ->
    match_simple_typ ~error ~changes env lvl {ctor=env_rigid_bound env rv;flexvars=[]} head);
  flexvars |> List.iter (fun fv ->
    let mhead = map_head id ignore head in
    let m = ensure_upper_matches ~error ~changes:(ref []) env fv {cons=mhead;rigvars=[]} in
    subtype_cons ~error:noerror m head
      ~neg:(fun _t () -> () (*already filled*))
      (* FIXME levels: fine as long as lvl = env_level env? Enforce? *)
      ~pos:(fun v r -> r := join_flexvars !r [v]));
  ()


let rec subtype ~error env (p : ptyp) (n : ntyp) =
  (* Format.printf "%a <= %a\n" pp_ptyp p pp_ntyp n; *)
  wf_ptyp env p; wf_ntyp env n;
  match p, n with
  | Tcons cp, Tcons cn ->
     subtype_cons ~error
       ~neg:(subtype ~error env)
       ~pos:(subtype ~error env)
       cp cn
  | p, Tpoly {vars; body} ->
     let level = Env_level.extend (env_level env) in
     let rvars = IArray.mapi (fun var _ -> {level; var}) vars in
     let rig_defns = IArray.map (fun (name, b) ->
       { name;
         upper = simple_ptyp_bound level (open_typ_rigid rvars b) }) vars in
     let body = open_typ_rigid rvars body in
     let env = Env_types { level; rig_names = SymMap.empty; rig_defns; rest = env} in
     subtype ~error env p body; ()
  | Tpoly {vars; body}, n ->
     let level = Env_level.extend (env_level env) in
     let env = Env_types { level; rig_names = SymMap.empty; rig_defns = IArray.empty; rest = env } in
     let body = instantiate_flex env vars body in
     subtype ~error env body n; ()
  | p, Tcons cn ->
     let shead = map_head (approx_ptyp env) (fun _ -> ref bottom) cn in
     match_simple_typ ~error ~changes:(ref []) env (env_level env) (approx_ptyp env p) shead;
     subtype_cons ~error:noerror shead cn
       ~neg:(fun _ _ -> () (* already done above *))
       ~pos:(fun p n -> subtype ~error env (Tsimple !p) n)
  | p, ((Tsimple _ | Tvar _ | Tvjoin _) as n) ->
     subtype_t_var ~error ~changes:(ref []) env (approx_ptyp env p) (approx_ntyp_var env n); ()

let rec match_typ ~error env lvl (p : ptyp) (head : (ntyp Ivar.put, ptyp Ivar.put) cons_head) =
  wf_ptyp env p;
  match p with
  | Tcons c ->
     subtype_cons ~error ~neg:(fun v t -> Ivar.put v t) ~pos:(fun t v -> Ivar.put v t) c head
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_typ ~error env lvl body head
  | t ->
     let instneg v =
       let fv = fresh_flexvar lvl in
       Ivar.put v (Tsimple fv);
       flexlb_fv fv in
     let shead = map_head instneg (fun _ -> ref bottom) head in
     match_simple_typ ~error ~changes:(ref []) env lvl (approx_ptyp env t) shead;
     subtype_cons ~error:noerror shead head
       ~neg:(fun _ _ -> () (*already inserted by instneg*))
       ~pos:(fun t v -> Ivar.put v (Tsimple !t));
     wf_ptyp env p;
     ()




(*
 * Generalisation
 *)

(* visit counters: odd = visiting, even = done *)

type visit_status = Unvisited | Visiting | Visited

let begin_visit_pos visit fv =
  assert (fv.pos_visit_count <= visit);
  if fv.pos_visit_count = visit - 1 then Visiting
  else if fv.pos_visit_count = visit then Visited
  else (fv.pos_visit_count <- visit - 1; Unvisited)

let end_visit_pos visit fv =
  assert (fv.pos_visit_count = visit - 1);
  fv.pos_visit_count <- visit

let begin_visit_neg visit fv =
  assert (fv.neg_visit_count <= visit);
  if fv.neg_visit_count = visit - 1 then
    intfail "neg cycle found on %s but rec types not implemented!" (flexvar_name fv)
  else if fv.neg_visit_count = visit then false
  else (fv.neg_visit_count <- visit - 1; true)

let end_visit_neg visit fv =
  assert (fv.neg_visit_count = visit - 1);
  fv.neg_visit_count <- visit

let is_visited_pos visit fv =
  assert (fv.pos_visit_count land 1 = 0);
  fv.pos_visit_count = visit

let is_visited_neg visit fv =
  assert (fv.neg_visit_count land 1 = 0);
  fv.neg_visit_count = visit


(* FIXME: I think this is all dodgy re flexvars at upper levels
   Are there enough level checks in expand / substn? *)
(* FIXME: how does this work with rigvars & flexvars at the same level? (i.e. poly fns) *)

let rec expand visit ~changes ?(vexpand=[]) env level (p : flex_lower_bound) =
  wf_flex_lower_bound ~seen:(Hashtbl.create 10) env level p;
  let ctor = map_ctor_rig (expand_fv_neg visit ~changes env level) (expand visit ~changes env level) p.ctor in
  let flexvars_gen, flexvars_keep = List.partition (fun fv -> Env_level.equal fv.level level) p.flexvars in
  flexvars_keep |> List.iter (fun fv ->
    (* Hoist to avoid making invalid Tvjoins later *)
    (* FIXME: pretty sure this can fail *)
    hoist_lower ~error:noerror ~changes env fv.level {p with flexvars=[]});
  flexvars_gen |> List.iter (fun pv ->
    match begin_visit_pos visit pv with
    | Visited -> ()
    | Unvisited ->
       ignore (flex_cons_upper ~changes env pv); (* ensure upper not UBvar *)
       (* Add pv to vexpand so we know to ignore it if we see it again before going
          under a constructor. (This is basically a bad quadratic SCC algorithm) *)
       let lower = expand visit ~changes ~vexpand:(pv :: vexpand) env level pv.lower in
       (* Remove useless reflexive constraints, if they appeared by expanding a cycle *)
       let lower = { lower with flexvars = List.filter (fun v -> not (equal_flexvar v pv)) lower.flexvars } in
       if fv_maybe_set_lower ~changes pv lower then
         ensure_rigvars_present ~changes env pv;
       end_visit_pos visit pv
    | Visiting ->
       (* recursive occurrences are fine if not under a constructor *)
       if List.memq pv vexpand then ()
       else unimp "positive recursion on flexvars");
  (* NB: flexvars_gen occurs twice below, re-adding the reflexive constraints: α expands to (α|α.lower) *)
  List.fold_left (fun p v -> join_lower ~error:noerror (*FIXME*) ~changes env level p v.lower)
    { ctor; flexvars = flexvars_keep @ flexvars_gen }
    flexvars_gen

and expand_fv_neg visit ~changes env level nv =
  if Env_level.equal nv.level level && begin_visit_neg visit nv then begin
    begin match nv.upper with
    | UBnone | UBcons [] -> ()
    | UBvar v -> ignore (expand_fv_neg visit ~changes env level v)
    | UBcons [cn] ->
       let upper = UBcons [map_ctor_rig (expand visit ~changes env level) (expand_fv_neg visit ~changes env level) cn] in
       let _:bool = fv_maybe_set_upper ~changes nv upper in
       ()
    | UBcons cns ->
       let cns = List.map (map_ctor_rig (expand visit ~changes env level) (expand_fv_neg visit ~changes env level)) cns in

       let all_rigvars =
         List.concat_map (fun c -> c.rigvars) cns |> List.sort_uniq compare_rigvar in
       let keep_rigvars = all_rigvars |> List.filter (fun rv ->
         cns |> List.for_all (fun cn ->
           let temp_changes = ref [] in
           let error _ = raise Exit in
           (* FIXME: speculative subtyping is very dodgy *)
           match subtype_ctor_rig ~error ~changes:temp_changes env
                   {cons=Bot; rigvars=[rv]} cn with
           | () when !temp_changes = [] -> true

           | () ->
              (* FIXME: which of these is less bad? *)
              revert !temp_changes; false
              (* commit ~changes !temp_changes; true *)

           | exception Exit -> revert !temp_changes; false
         )) in

       fv_set_upper ~changes nv (UBcons []);
       cns |> List.iter (fun cn ->
         subtype_flex_cons ~error:noerror ~changes env nv {cn with rigvars = keep_rigvars })
    end;
    end_visit_neg visit nv
  end;
  nv

(* FIXME: could expand and subst be the same function?
   subst by referring to *previous* visit state, keep going until fixpoint.\
   (Assumption: if a variable wasn't reachable with a given polarity on pass 1,
    then it will never be reachable with that polarity) *)

let rec expand_ptyp visit ~changes env level (p : ptyp) =
  match p with
  | Tcons c -> Tcons (map_head (expand_ntyp visit ~changes env level) (expand_ptyp visit ~changes env level) c)
  | Tsimple s -> Tsimple (expand visit ~changes env level s)
  | Tvar (Vbound v) -> Tvar (Vbound v)
  | Tvjoin (t, Vbound v) -> Tvjoin (expand_ptyp visit ~changes env level t, Vbound v)
  | Tvjoin (_, (Vflex _ | Vrigid _)) | Tvar (Vflex _ | Vrigid _) ->
     (* must be locally closed since inside tvjoin flex/rigid *)
     Tsimple (expand visit ~changes env level (simple_ptyp level p))
  | Tpoly {vars; body} ->
     let vars = IArray.map (fun (s, t) -> s, expand_ntyp visit ~changes env level t) vars in
     let body = expand_ptyp visit ~changes env level body in
     Tpoly {vars; body}

and expand_ntyp visit ~changes env level (n : ntyp) =
  match n with
  | Tcons c -> Tcons (map_head (expand_ptyp visit ~changes env level) (expand_ntyp visit ~changes env level) c)
  | Tsimple s -> Tsimple (expand_fv_neg visit ~changes env level s)
  | Tvar (Vflex fv) when Env_level.equal fv.level level ->
     Tvar (Vflex (expand_fv_neg visit ~changes env level fv))
  | Tvar v -> Tvar v
  | Tvjoin (t, (Vbound _ | Vrigid _ as v)) ->
     Tvjoin (expand_ntyp visit ~changes env level t, v)
  | Tvjoin (_, Vflex _) -> intfail "expand_ntyp: unexpected Vflex"
  | Tpoly {vars; body} ->
     let vars = IArray.map (fun (s, t) -> s, expand_ptyp visit ~changes env level t) vars in
     let body = expand_ntyp visit ~changes env level body in
     Tpoly {vars; body}

(* FIXME: bit weird... There must be a better representation for bvars here *)
type genvar =
  | Gen_flex of flexvar * ntyp ref
  | Gen_rigid of rigvar


let rec substn visit bvars level ~index ({ctor={cons;rigvars};flexvars} : flex_lower_bound) : ptyp =
  let cons = map_head (substn_fv_neg visit bvars level ~index) (substn visit bvars level ~index) cons in
  let rigvars_gen, rigvars_keep = List.partition (fun (rv:rigvar) -> Env_level.equal rv.level level) rigvars in
  let flexvars_gen, flexvars_keep = List.partition (fun (fv:flexvar) -> Env_level.equal fv.level level) flexvars in

  let rigvars_gen = rigvars_gen |> List.map (fun (rv:rigvar) ->
    Vbound {index; var = rv.var}) in
  let rigvars_keep = rigvars_keep |> List.map (fun rv -> Vrigid rv) in
  let flexvars_gen = flexvars_gen |> List.filter_map (fun pv ->
    if is_visited_neg visit pv then
      Some (Vbound {index; var = substn_bvar visit bvars level pv})
    else None) in
  let flexvars_keep = flexvars_keep |> List.map (fun fv -> Vflex fv) in

  (* FIXME: are Tvjoin invariants OK here? Should I sort the _keep vars? *)
  (* FIXME: if cons = bot, should we avoid the tvjoin? *)
  List.fold_left
    (fun rest var -> Tvjoin (rest, var))
    (Tcons cons)
    (rigvars_keep @ flexvars_keep @ rigvars_gen @ flexvars_gen)

and substn_fv_neg visit bvars level ~index nv : ntyp =
  assert (Env_level.extends nv.level level);
  if Env_level.equal nv.level level then begin
    assert (is_visited_neg visit nv);
    if is_visited_pos visit nv then
      Tvar (Vbound { index;
                     var = substn_bvar visit bvars level nv })
    else substn_upper visit bvars level ~index nv.upper
  end else begin
    Tvar (Vflex nv)
  end

and substn_upper visit bvars level ~index = function
  | UBvar v -> substn_fv_neg visit bvars level ~index v
  | UBnone | UBcons [] -> Tcons Top
  | UBcons (_ :: _ :: _) -> intfail "multirig gen"
  | UBcons [{cons;rigvars}] ->
     let cons = map_head (substn visit bvars level ~index) (substn_fv_neg visit bvars level ~index) cons in
     let rigvars_gen, rigvars_keep = List.partition (fun (rv:rigvar) -> Env_level.equal rv.level level) rigvars in
     (* Drop rigvars_gen if needed to avoid contravariant joins. *)
     match cons, rigvars_keep, rigvars_gen with
     | Bot, [], [v] ->
        assert (Vector.get bvars v.var = Gen_rigid v);
        Tvar (Vbound {index; var=v.var})
     | cons, rigvars, _ ->
        (* FIXME: should the rigvars be sorted? Should this be kept as Tsimple somehow? *)
        List.fold_left (fun c r -> Tvjoin (c, Vrigid r)) (Tcons cons) rigvars


(* FIXME!!: gen constraints. What can upper bounds be? *)
and substn_bvar visit bvars level fv =
  assert (Env_level.equal fv.level level);
  assert (is_visited_neg visit fv && is_visited_pos visit fv);
  if fv.bound_var = -2 then unimp "flexvar recursive in own bound";
  if fv.bound_var <> -1 then fv.bound_var else begin
    let r = ref (Tcons Top) in
    fv.bound_var <- -2;
    r := substn_upper visit bvars level ~index:0 fv.upper;
    let n = Vector.push bvars (Gen_flex (fv, r)) in
    fv.bound_var <- n;
    n
  end

(* FIXME: deja vu? *)
let rec substn_ptyp visit bvars level ~index : ptyp -> ptyp = function
  | Tcons c -> Tcons (map_head (substn_ntyp visit bvars level ~index)
                        (substn_ptyp visit bvars level ~index) c)
  | Tsimple s -> substn visit bvars level ~index s
  | Tvar (Vbound v) -> Tvar (Vbound v)
  | Tvjoin (t, Vbound v) -> Tvjoin (substn_ptyp visit bvars level ~index t, Vbound v)

  | Tvjoin (_, (Vflex _ | Vrigid _)) | Tvar (Vflex _ | Vrigid _) as p ->
     (* must be locally closed since inside tvjoin flex/rigid *)
     (substn visit bvars level ~index (simple_ptyp level p))
  | Tpoly {vars;body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (s,t) -> s, substn_ntyp visit bvars level ~index t) vars in
     let body = substn_ptyp visit bvars level ~index body in
     Tpoly {vars; body}

and substn_ntyp visit bvars level ~index : ntyp -> ntyp = function
  | Tcons c -> Tcons (map_head (substn_ptyp visit bvars level ~index)
                        (substn_ntyp visit bvars level ~index) c)
  | Tsimple s -> substn_fv_neg visit bvars level ~index s
  | Tvar (Vbound v) -> Tvar (Vbound v)
  | Tvjoin (t, Vbound v) ->
     Tvjoin (substn_ntyp visit bvars level ~index t, Vbound v)

  | Tvjoin (_, (Vflex _ | Vrigid _)) | Tvar (Vflex _ | Vrigid _) as n ->
     (* must be locally closed since inside tvjoin flex/rigid *)
     substn_upper visit bvars level ~index (simple_ntyp level n)

  | Tpoly {vars;body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (s,t) -> s, substn_ptyp visit bvars level ~index t) vars in
     let body = substn_ntyp visit bvars level ~index body in
     Tpoly {vars; body}
