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



(* FIXME: does this need separate ~neg and ~pos? *)
(* FIXME: Inline into single use site? *)


(*
 * Core subtyping functions
 *)



let fresh_flexvar level = fresh_flexvar_gen level UBnone

(* equivalent to making a fresh var and constraining <= fv
   fv must be at or below lvl *)
let fresh_below_var lvl fv =
  assert (Env_level.extends fv.level lvl);
  fresh_flexvar_gen lvl (UBvar fv)

(* equivalent to making a fresh var and constraining <= cn
   cn must be wf at lvl. FIXME: check this thoroughly *)
let fresh_below_cons lvl {cons;rigvars} =
  List.iter (fun (rv : rigvar) -> assert (Env_level.extends rv.level lvl)) rigvars;
  (* need to freshen covariant parts of cons to preserve matchability.
     FIXME: is that true for double-negative parts as well?
     What's the matchability status of the flexvars embedded in the flex_lower_bound?
     I don't think we assume it below, we always join there rather than matching. Verify. *)
  let cons = map_head id (fresh_below_var lvl) cons in
  fresh_flexvar_gen lvl (UBcons {cons;rigvars})

(* add some flexvars to a join.
   does not check levels, so level of resulting join may increase *)
let join_flexvars ~changed lower vs =
  if lower.ctor.cons = Top then lower
  else
    match List.filter (fun v -> not (List.memq v lower.flexvars)) vs with
    | [] -> lower
    | vs -> changed := true; { lower with flexvars = lower.flexvars @ vs }

(* Convert a flexvar's upper bound to UBcons form. May decrease levels. *)
let rec flex_cons_upper ~changed env (fv : flexvar) : (flex_lower_bound, flexvar) ctor_ty =
  match fv.upper with
  | UBcons c -> c
  | UBnone ->
     let triv = { cons = Top; rigvars = [] } in
     changed := true;
     fv.upper <- UBcons triv;
     triv
  | UBvar v ->
     (* FIXME rectypes & ordering. Prevent UBvar cycles somehow? *)
     changed := true;
     assert (fv.lower = { ctor = { cons = Bot; rigvars = [] } ; flexvars = [] });
     assert (Env_level.extends v.level fv.level);
     let upper = flex_cons_upper ~changed env v in (* NB: may hoist v! *)
     if not (Env_level.equal v.level fv.level) then begin
       (* Hoist fv. Bounds known trivial, so no work needed there *)
       fv.level <- v.level
     end;
     v.lower <- join_flexvars ~changed v.lower [fv]; (* wf: levels equal *)
     (* To preserve matchability, need to freshen the strictly covariant variables in pv.upper. *)
     (* FIXME: why only strictly covariant? Is there a bug here?
        How are the non-strictly-covariant ones joined?
        See also fresh_below_cons, same deal. *)
     (* No hoisting needed since we're at the same level as v *)
     let upper = map_ctor_rig id (fresh_below_var fv.level) upper in
     fv.upper <- UBcons upper;
     upper


let rec subtype_t_var ~error ~changed env (p : flex_lower_bound) (nv : flexvar) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_flex ~error ~changed env pv nv);
  subtype_cons_flex ~error ~changed env p.ctor nv

and subtype_t_cons ~error ~changed env (p : flex_lower_bound) (cn : (flex_lower_bound, flexvar) ctor_ty) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_cons ~error ~changed env pv cn);
  subtype_ctor_rig ~error ~changed env p.ctor cn

and subtype_ctor_rig ~error ~changed env cp cn =
  cp.rigvars |> List.iter (fun pv ->
    if contains_rigvar pv cn.rigvars then ()
    else subtype_ctor_rig ~error ~changed env (env_rigid_bound env pv) cn);
  subtype_cons ~error
    ~neg:(subtype_t_var ~error ~changed env)
    ~pos:(subtype_t_var ~error ~changed env) cp.cons cn.cons;
  ()

and subtype_flex_flex ~error ~changed env (pv : flexvar) (nv : flexvar) =
  match pv.upper with
  | _ when List.memq pv nv.lower.flexvars -> ()
  | UBvar nv' when nv == nv' ->
     (* FIXME there are more cases we could ignore! *)
     ()
  | UBnone when Env_level.extends nv.level pv.level ->
     changed := true;
     pv.upper <- UBvar nv; (* FIXME: can this make a cycle? *)
     subtype_t_var ~error ~changed env pv.lower nv
  | _ ->
     (* FIXME detect other no-op cases *)
     (* FIXME rectypes support affected by ordering here *)
     let upper = flex_cons_upper ~changed env nv in
     nv.lower <- join_flexvars ~changed nv.lower [pv];
     (* FIXME: maybe flex_cons_upper should return level? TOCTOU otherwise *)
     (* FIXME: ordering of side-effects here *)
     hoist_flex ~changed env nv.level pv;
     assert (Env_level.extends pv.level nv.level);
     subtype_flex_cons ~error ~changed env pv upper

and subtype_flex_cons ~error ~changed env pv cn =
  let cp = ensure_upper_matches ~error ~changed env pv (map_ctor_rig id ignore cn) in
  subtype_cons ~error
    ~neg:(fun _ () -> () (* already done in ensure_upper_matches *))
    ~pos:(subtype_flex_flex ~error ~changed env)
    cp cn.cons

(* Ensure pv has a UBcons upper bound whose head is below a given ctor.
   Returns the constructed upper bound.
   FIXME: poly rather than unit for cn's type *)
and ensure_upper_matches ~error ~changed env (pv : flexvar) (cn : (flex_lower_bound, unit) ctor_ty) : (unit, flexvar) cons_head =
  let cb = flex_cons_upper ~changed env pv in
  let changed' = ref false in
  let cons =
    meet_cons
      ~nleft:id
      ~nright:(fun b -> join_lower ~changed:changed' env pv.level bottom b) (* FIXME bad hoist fn *)
      ~nboth:(fun a b -> join_lower ~changed:changed' env pv.level a b)
      ~pleft:id
      ~pright:(fun _ -> fresh_flexvar pv.level)
      ~pboth:(fun v _ -> v)
      cb.cons cn.cons in
  (* FIXME: there are better ways to compute this *)
  if (map_head ignore ignore cb.cons <> map_head ignore ignore cons)
  then changed' := true;

  let cn' =
    (* FIXME: maybe compute this lazily? *)
    (* same ctor as cn, but with flexvars filled in *)
    join_cons
      ~nleft:id
      ~nright:(fun _ -> assert false)
      ~nboth:(fun cn _ -> cn)
      ~pleft:(fun _ -> fresh_flexvar (env_level env)) (* ignore, but var required *)
      ~pright:(fun _ -> assert false)
      ~pboth:(fun () v -> v)
      cn.cons cons in
(*
  if (map_head ignore ignore cn.cons <> map_head ignore ignore cn') then begin
    let prcons c =
      unparse_cons ~neg:(fun _ -> mktyexp (named_type "_")) ~pos:(fun _ -> mktyexp (named_type "_")) c 
      |> Print.tyexp
      |> (fun x -> PPrint.(ToChannel.pretty 1. 120 stderr (x ^^ hardline))) in
    prcons cb.cons; 
    prcons cn.cons;
    prcons cons;
    prcons cn';
    Printf.fprintf stderr "bang\n%!";
  end;
*)
  (* should be true by absorption law *)
  assert (map_head ignore ignore cn.cons = map_head ignore ignore cn');

  let rigvars =
    (* Dragons. *)
    (* FIUATT: should this call spec_sub unconditionally? Probably not. *)
    let spec_sub rv c =
      (* FIXME can speculative subtyping screw things up? Probably...
         The speculation seems unreliable, as whether it gets done must surely
         depend on constraint resolution order (due to width subtyping).
         So any changes we make during (failed?) speculation are suspect.
         Should they be backed out if they don't work? *)
      (* FIXME: Write some tests that actually observe weirdness here (tricky...) *)
      let error _ = raise Exit in
      match subtype_ctor_rig ~error ~changed env (env_rigid_bound env rv) c with
      | () -> true
      | exception Exit -> false in
    let cbrig =
      cb.rigvars |> List.filter (fun vb ->
        if contains_rigvar vb cn.rigvars then true
        else spec_sub vb {cn with cons = cn'}) in
    let cnrig =
      cn.rigvars |> List.filter (fun vn ->
        if contains_rigvar vn cb.rigvars then false (* already included *)
        else if not (Env_level.extends vn.level pv.level) then false (* scope escape *)
        else spec_sub vn cb) in
    cbrig @ cnrig in
  if rigvars <> cb.rigvars then changed' := true;

  assert (!changed' || cb = {cons; rigvars}); (* FIXME poly eq *)
  if !changed' then begin
    changed := true;
    let bound = { cons; rigvars } in
    (* FIXME is this all still wf, despite hoisting? *)
    pv.upper <- UBcons bound;
    subtype_t_cons ~error ~changed env pv.lower bound;
    wf_ptyp env (Tsimple (flexlb_fv pv));
  end;
  map_head ignore id cons

and subtype_cons_flex ~error ~changed env (cp : (flexvar, flex_lower_bound) ctor_ty) (nv : flexvar) =
  match cp with
  | { cons = Bot; rigvars = [] } ->
     (* avoid even calling flex_cons_upper in the trivial case *)
     ()
  | cp ->
     let changed' = ref false in
     let bound = flex_cons_upper ~changed:changed' env nv in
     nv.lower <- join_ctor ~changed:changed' env nv.level nv.lower cp;
     (* FIXME: should it be enough to compare cp instead of nv.lower?
        Can we ditch changed' then? Probably better not to. *)
     if !changed' then begin
       changed := true;
       subtype_t_cons ~error ~changed env nv.lower bound
     end

and join_ctor ~changed env level lower cp =
  (* lower is already wf at level, cp may not be *)
  (* FIXME hoisting: hoist cp flexvars if needed *)
  let cons =
    join_cons
       ~nleft:id
       ~nright:(fun y ->
         (* Not fresh_below_var, as hoisting may be needed.
            FIXME test this *)
         let v = fresh_flexvar level in subtype_flex_flex ~error:noerror ~changed env v y; v)
       ~nboth:(fun x y -> subtype_flex_flex ~error:noerror ~changed env x y; x)
       ~pleft:id
       (* NB: pright is not id, because we need fresh variables for contravariant parts,
          to preserve matchability *)
       ~pright:(fun x -> join_lower ~changed env level bottom x)
       ~pboth:(fun x y -> join_lower ~changed env level x y)
       lower.ctor.cons cp.cons in
  if (map_head ignore ignore lower.ctor.cons <> map_head ignore ignore cons) then changed := true;
  (* FIXME: Top case of rigvars? check. *)
  List.fold_left (fun c rv ->
    if contains_rigvar rv c.ctor.rigvars then c
    else if Env_level.extends rv.level level then begin
      changed := true;
      { c with ctor = { c.ctor with rigvars = c.ctor.rigvars @ [rv] } }
    end else
      join_ctor ~changed env level c (env_rigid_bound env rv))
    { ctor = {cons; rigvars = lower.ctor.rigvars }; flexvars = lower.flexvars}  cp.rigvars
  
and join_lower ~changed env level lower {ctor; flexvars} =
  let ctor = join_ctor ~changed env level lower ctor in
  List.iter (hoist_flex ~changed env level) flexvars;
  let lb = join_flexvars ~changed ctor flexvars in
  (* wf_flex_lower_bound ~seen:(Hashtbl.create 10) env level lower; *)
  lb


and hoist_flex ~changed env level v =
  if Env_level.extends v.level level then ()
  else match v.upper with
    | UBnone ->
       changed := true; v.level <- level
    | UBvar v' when Env_level.extends v'.level level ->
       changed := true; v.level <- level
    | _ ->
       let cn = flex_cons_upper ~changed env v in
       (* FIXME hoist vs. copy differs slightly for contravariant components.
          Does this matter? *)
       if Env_level.extends v.level level then
         intfail "everything's fine, but hitting this case is impressive"
       else begin
         changed := true;
         v.level <- level;
         v.upper <- UBcons (map_ctor_rig (join_lower ~changed env level bottom) (fun v -> hoist_flex ~changed env level v; v) cn);
         hoist_lower ~changed env level v.lower;
         (* FIXME hoisting: recheck *)
       end

and hoist_lower ~changed env level {ctor;flexvars} =
  map_ctor_rig (hoist_flex ~changed env level) (hoist_lower ~changed env level) ctor |> ignore;
  List.iter (hoist_flex ~changed env level) flexvars;
  ()

(* FIXME hoisting below here *)


(*
 * Subtyping on typs (polymorphism)
 *)

(* argument must be a simple locally closed type well-formed at lvl *)
let rec simple_ptyp lvl : ptyp -> flex_lower_bound = function
  | Tsimple t -> t
  | Tcons cp ->
     let cons = map_head (simple_ntyp_var lvl) (simple_ptyp lvl) cp in
     { ctor = { cons; rigvars = [] } ; flexvars = [] }
  | Tpoly _ -> intfail "simple_ptyp: Tpoly is not simple"
  | Tvjoin (_, Vbound _) | Tvar (Vbound _) -> intfail "simple_ptyp: not locally closed"
  | Tvar (Vflex fv) -> { ctor = {cons=Bot;rigvars=[]}; flexvars = [fv] }
  | Tvar (Vrigid rv) -> { ctor = {cons=Bot; rigvars=[rv]}; flexvars = [] }
  | Tvjoin (t, Vflex fv) ->
     assert (Env_level.extends fv.level lvl);
     join_flexvars ~changed:(ref false) (simple_ptyp fv.level t) [fv]
  | Tvjoin (t, Vrigid rv) ->
     assert (Env_level.extends rv.level lvl);
     let {ctor={cons;rigvars};flexvars} = simple_ptyp rv.level t in
     {ctor={cons;rigvars=if contains_rigvar rv rigvars then rigvars else rv::rigvars};flexvars}

and simple_ntyp lvl : ntyp -> styp_neg = function
  | Tsimple t -> UBvar t
  | Tcons Top -> UBnone
  | Tcons cn ->
     UBcons {cons = map_head (simple_ptyp lvl) (simple_ntyp_var lvl) cn; rigvars=[]}
  | Tpoly _ -> intfail "simple_ntyp: Tpoly is not simple"
  | Tvjoin (_, Vbound _) | Tvar (Vbound _) -> intfail "simple_ntyp: not locally closed"
  | Tvar (Vflex fv) -> UBvar fv
  | Tvar (Vrigid rv) -> UBcons {cons=Bot; rigvars=[rv]}
  | Tvjoin (_, Vflex _) -> intfail "simple_ntyp: negative join"
  | Tvjoin (t, Vrigid rv) ->
     assert (Env_level.extends rv.level lvl);
     match simple_ntyp rv.level t with
     | UBnone -> UBnone
     | UBvar _ -> intfail "simple_ntyp: rigid/flex negative join"
     | UBcons {cons;rigvars} ->
        let rigvars = if contains_rigvar rv rigvars then rigvars else rv::rigvars in
        UBcons {cons;rigvars}

and simple_ntyp_var lvl (t : ntyp) : flexvar =
  match simple_ntyp lvl t with
  | UBnone -> fresh_flexvar lvl
  | UBvar v -> v
  | UBcons cn -> fresh_below_cons lvl cn


let simple_ntyp_bound lvl t =
  match simple_ntyp lvl t with
  | UBnone -> { cons = Top; rigvars = [] }
  | UBcons c -> c
  | UBvar _ -> intfail "simple_ntyp_bound: flexvars present in bound"

let instantiate_flex env vars body =
  let level = env_level env in
  let fvars = IArray.map (fun _ -> fresh_flexvar level) vars in
  IArray.iter2 (fun fv (_, b) ->
    (* FIXME: use fresh_below? *)
    let b = simple_ntyp_bound (env_level env) (open_typ_flex fvars b) in
    subtype_t_cons ~error:noerror ~changed:(ref false) env (flexlb_fv fv) b
  ) fvars vars;
  open_typ_flex fvars body

(* arg must be locally closed, not necessarily simple *)
let rec approx_ptyp env : ptyp -> flex_lower_bound = function
  | Tcons cp ->
     let cons = map_head (approx_ntyp env) (approx_ptyp env) cp in
     { ctor = { cons; rigvars = [] }; flexvars = [] }
  | (Tvar _ | Tvjoin _ | Tsimple _) as t -> simple_ptyp (env_level env) t
  | Tpoly {vars;body} ->
     let body = instantiate_flex env vars body in
     approx_ptyp env body

and approx_ntyp env : ntyp -> flexvar = function
  | Tcons cn ->
     let cons = map_head (approx_ptyp env) (approx_ntyp env) cn in
     let fv = fresh_flexvar (env_level env) in
     subtype_flex_cons ~error:noerror ~changed:(ref false) env fv {cons;rigvars=[]};
     fv
  | (Tvar _ | Tvjoin _ | Tsimple _) as t -> simple_ntyp_var (env_level env) t
  | Tpoly _ -> unimp "approx_ntyp: Tpoly"


let simple_ptyp_bound lvl t =
  match simple_ptyp lvl t with
  | { ctor; flexvars = [] } -> ctor
  | _ -> intfail "simple_ptyp_bound: flexvars present in bound"


let rec subtype ~error env (p : ptyp) (n : ntyp) =
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
     (* FIXME: which env does simple_ptyp_bound run in? *)
     let rig_defns = IArray.map (fun (name, b) ->
       { name;
         upper = simple_ptyp_bound (env_level env) (open_typ_rigid rvars b) }) vars in
     let body = open_typ_rigid rvars body in
     let env = Env_types { level; rig_names = SymMap.empty; rig_defns; rest = env} in
     subtype ~error env p body
  | Tpoly {vars; body}, n ->
     let level = Env_level.extend (env_level env) in
     let env = Env_types { level; rig_names = SymMap.empty; rig_defns = IArray.empty; rest = env } in
     let body = instantiate_flex env vars body in
     subtype ~error env body n
  | p, Tcons cn ->
     (* FIXME duplicate subtype_t_cons and subtype_flex_cons for better matching behaviour here *)
     subtype_t_var ~error ~changed:(ref false) env (approx_ptyp env p) (approx_ntyp env (Tcons cn))
  | p, n -> subtype_t_var ~error ~changed:(ref false) env (approx_ptyp env p) (approx_ntyp env n)


let rec match_typ ~error env lvl (p : ptyp) (orig_head : (ntyp Ivar.put, ptyp Ivar.put) cons_head) =
  wf_ptyp env p;
  match p with
  | Tcons c ->
     subtype_cons ~error ~neg:(fun v t -> Ivar.put v t) ~pos:(fun t v -> Ivar.put v t) c orig_head
(* FIXME unneeded, approx_ptyp works? Nah, predicativity bad.  | Tpoly _ -> unimp "instantiate on poly match" *)
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_typ ~error env lvl body orig_head
  | t ->
     let {ctor; flexvars} = approx_ptyp env t in
     wf_ptyp env p;
     let head =
       map_head
         (fun iv -> let v = fresh_flexvar lvl in
                    Ivar.put iv (Tsimple v);
                    flexlb_fv v)
         ignore
         orig_head in
     let fv = match ctor, flexvars with { cons = Bot; rigvars = []}, [fv] -> fv | _ -> unimp "match" in
     (* FIXME: unify with subtype_flex_cons? *)
     let m = ensure_upper_matches ~error ~changed:(ref false) env fv {cons=head;rigvars=[]} in
     wf_ptyp env (Tsimple {ctor;flexvars});
     subtype_cons ~error:noerror
       ~neg:(fun _t () -> () (*already filled*))
       ~pos:(fun p' t' -> Ivar.put t' (Tsimple (flexlb_fv p')))
       m orig_head;
     wf_ptyp env p;
     ()

(* FIXME: rank1 joins maybe?
   FIXME: keep types as Tcons if possible? Better inference. Can this matter? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  let p = approx_ptyp env p and q = approx_ptyp env q in
  let r = bottom in
  let r = join_lower ~changed:(ref false) env (env_level env) r p in
  let r = join_lower ~changed:(ref false) env (env_level env) r q in
  Tsimple r










(*
 * Generalisation
 *)

(* visit counters: odd = visiting, even = done *)

let begin_visit_pos visit fv =
  assert (fv.pos_visit_count <= visit);
  if fv.pos_visit_count = visit - 1 then
    intfail "pos cycle found on %s but rec types not implemented!" (flexvar_name fv)
  else if fv.pos_visit_count = visit then false
  else (fv.pos_visit_count <- visit - 1; true)

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

let rec expand visit ~changed env level (p : flex_lower_bound) =
  let ctor = map_ctor_rig (expand_fv_neg visit ~changed env level) (expand visit ~changed env level) p.ctor in
  let flexvars = p.flexvars in
  flexvars |> List.iter (fun pv ->
    (* FIXME kinda quadratic *)
    (* FIXME: contravariant hoisting? Curried choose type? *)
    hoist_lower ~changed env pv.level p;
    if Env_level.equal pv.level level && begin_visit_pos visit pv then begin
      ignore (flex_cons_upper ~changed env pv); (* ensure upper not UBvar *)
      pv.lower <- expand visit ~changed env level pv.lower;
      end_visit_pos visit pv
    end);
  List.fold_left (fun p v -> join_lower ~changed env level p v.lower) { ctor; flexvars } flexvars

and expand_fv_neg visit ~changed env level nv =
  if Env_level.equal nv.level level && begin_visit_neg visit nv then begin
    begin match nv.upper with
    | UBnone -> ()
    | UBvar v -> ignore (expand_fv_neg visit ~changed env level v)
    | UBcons cn ->
       nv.upper <- UBcons (map_ctor_rig (expand visit ~changed env level) (expand_fv_neg visit ~changed env level) cn)
    end;
    end_visit_neg visit nv
  end;
  nv

(* FIXME: could expand and subst be the same function?
   subst by referring to *previous* visit state, keep going until fixpoint.\
   (Assumption: if a variable wasn't reachable with a given polarity on pass 1,
    then it will never be reachable with that polarity) *)

let rec expand_ptyp visit ~changed env level (p : ptyp) =
  match p with
  | Tcons c -> Tcons (map_head (expand_ntyp visit ~changed env level) (expand_ptyp visit ~changed env level) c)
  | Tsimple s -> Tsimple (expand visit ~changed env level s)
  | Tvar (Vbound v) -> Tvar (Vbound v)
  | Tvjoin (t, Vbound v) -> Tvjoin (expand_ptyp visit ~changed env level t, Vbound v)
  | Tvjoin (_, (Vflex _ | Vrigid _)) | Tvar (Vflex _ | Vrigid _) ->
     (* must be locally closed since inside tvjoin flex/rigid *)
     Tsimple (expand visit ~changed env level (simple_ptyp level p))
  | Tpoly {vars; body} ->
     let vars = IArray.map (fun (s, t) -> s, expand_ntyp visit ~changed env level t) vars in
     let body = expand_ptyp visit ~changed env level body in
     Tpoly {vars; body}

and expand_ntyp visit ~changed env level (n : ntyp) =
  match n with
  | Tcons c -> Tcons (map_head (expand_ptyp visit ~changed env level) (expand_ntyp visit ~changed env level) c)
  | Tsimple s -> Tsimple (expand_fv_neg visit ~changed env level s)
  | Tvar (Vflex fv) when Env_level.equal fv.level level ->
     Tvar (Vflex (expand_fv_neg visit ~changed env level fv))
  | Tvar v -> Tvar v
  | Tvjoin (t, (Vbound _ | Vrigid _ as v)) ->
     Tvjoin (expand_ntyp visit ~changed env level t, v)
  | Tvjoin (_, Vflex _) -> intfail "expand_ntyp: unexpected Vflex"
  | Tpoly {vars; body} ->
     let vars = IArray.map (fun (s, t) -> s, expand_ptyp visit ~changed env level t) vars in
     let body = expand_ntyp visit ~changed env level body in
     Tpoly {vars; body}


(* FIXME dodgy as fuck tvjoin *)
let tcons {cons;rigvars} =
  List.fold_left (fun c r -> Tvjoin (c, Vrigid r)) (Tcons cons) rigvars

let rec substn visit bvars level ~index ({ctor;flexvars} : flex_lower_bound) : ptyp =
  let cons = map_ctor_rig (substn_fv_neg visit bvars level ~index) (substn visit bvars level ~index) ctor in
  let flexvars = flexvars |> List.filter_map (fun pv ->
    assert (Env_level.extends pv.level level);
    (* FIXME: may want to sort these *)
    if not (Env_level.equal pv.level level) then
      Some (Vflex pv)
    else if is_visited_neg visit pv then
      Some (Vbound {index; var = substn_bvar visit bvars level ~index pv})
    else None) in
  List.fold_left (fun rest var -> Tvjoin (rest, var)) (tcons cons) flexvars

and substn_fv_neg visit bvars level ~index nv : ntyp =
  assert (Env_level.extends nv.level level);
  if Env_level.equal nv.level level then begin
    assert (is_visited_neg visit nv);
    if is_visited_pos visit nv then
      Tvar (Vbound { index;
                     var = substn_bvar visit bvars level ~index nv })
    else substn_upper visit bvars level ~index nv.upper
  end else begin
    Tvar (Vflex nv)
  end

and substn_upper visit bvars level ~index = function
  | UBvar v -> substn_fv_neg visit bvars level ~index v
  | UBnone -> Tcons Top
  | UBcons c -> tcons (map_ctor_rig (substn visit bvars level ~index) (substn_fv_neg visit bvars level ~index) c)

(* FIXME!!: gen constraints. What can upper bounds be? *)
and substn_bvar visit bvars level ~index fv =
  assert (is_visited_neg visit fv && is_visited_pos visit fv);
  if fv.bound_var <> -1 then fv.bound_var else begin
    let r = ref (Tcons Top) in
    let n = Vector.push bvars (fv, r) in
    fv.bound_var <- n;
    r := substn_upper visit bvars level ~index fv.upper;
    n
  end

(* FIXME: deja vu? *)
let rec substn_ptyp visit bvars level ~index : ptyp -> ptyp = function
  | Tcons c -> Tcons (map_head (substn_ntyp visit bvars level ~index)
                        (substn_ptyp visit bvars level ~index) c)
  | Tsimple s -> substn visit bvars level ~index s
  | Tvjoin (_, (Vflex _ | Vrigid _)) | Tvar (Vflex _ | Vrigid _) as p ->
     (* must be locally closed since inside tvjoin flex/rigid *)
     (substn visit bvars level ~index (simple_ptyp level p))
  | Tvjoin (t, Vbound v) -> Tvjoin (substn_ptyp visit bvars level ~index t, Vbound v)
  | Tvar (Vbound v) -> Tvar (Vbound v)
  | Tpoly {vars;body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (s,t) -> s, substn_ntyp visit bvars level ~index t) vars in
     let body = substn_ptyp visit bvars level ~index body in
     Tpoly {vars; body}

and substn_ntyp visit bvars level ~index : ntyp -> ntyp = function
  | Tcons c -> Tcons (map_head (substn_ptyp visit bvars level ~index)
                        (substn_ntyp visit bvars level ~index) c)
  | Tsimple s -> substn_fv_neg visit bvars level ~index s
  | Tvar (Vflex fv) (*FIXME when Env_level.equal fv.level level*) ->
     substn_fv_neg visit bvars level ~index fv
  | Tvar (Vbound v) -> Tvar (Vbound v)
  | Tvar _ -> unimp "substn tvar"
  | Tvjoin _ -> unimp "substn tvjoin"
  | Tpoly {vars;body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (s,t) -> s, substn_ptyp visit bvars level ~index t) vars in
     Tpoly {vars; body}
