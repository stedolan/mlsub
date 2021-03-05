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
let join_flexvars lower vs =
  if lower.ctor.cons = Top then lower
  else
    match List.filter (fun v -> not (List.memq v lower.flexvars)) vs with
    | [] -> lower
    | vs -> { lower with flexvars = lower.flexvars @ vs }

(* Convert a flexvar's upper bound to UBcons form. May decrease levels. *)
let rec flex_cons_upper ~changes env (fv : flexvar) : (flex_lower_bound, flexvar) ctor_ty =
  match fv.upper with
  | UBcons c -> c
  | UBnone ->
     let triv = { cons = Top; rigvars = [] } in
     fv_set_upper ~changes fv (UBcons triv);
     triv
  | UBvar v ->
     (* FIXME rectypes & ordering. Prevent UBvar cycles somehow? *)
     assert (fv.lower = { ctor = { cons = Bot; rigvars = [] } ; flexvars = [] });
     assert (Env_level.extends v.level fv.level);
     let upper = flex_cons_upper ~changes env v in (* NB: may hoist v! *)
     if not (Env_level.equal v.level fv.level) then begin
       (* Hoist fv. Bounds known trivial, so no work needed there *)
       fv_set_level ~changes fv v.level
     end;
     (* ~changes: don't really care, already logging fv *)
     fv_set_lower ~changes v (join_flexvars v.lower [fv]); (* wf: levels equal *)
     (* To preserve matchability, need to freshen the strictly covariant variables in pv.upper. *)
     (* FIXME: why only strictly covariant? Is there a bug here?
        How are the non-strictly-covariant ones joined?
        See also fresh_below_cons, same deal. *)
     (* No hoisting needed since we're at the same level as v *)
     let upper = map_ctor_rig id (fresh_below_var fv.level) upper in
     fv_set_upper ~changes fv (UBcons upper);
     upper


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
  match pv.upper with
  | _ when List.memq pv nv.lower.flexvars -> ()
  | UBvar nv' when nv == nv' ->
     (* FIXME there are more cases we could ignore! *)
     ()
  | UBnone when Env_level.extends nv.level pv.level ->
     fv_set_upper ~changes pv (UBvar nv); (* FIXME: can this make a cycle? *)
     subtype_t_var ~error ~changes env pv.lower nv
  | _ ->
     (* FIXME rectypes support affected by ordering here *)
     let upper = flex_cons_upper ~changes env nv in
     (* FIXME: what if pv <= UBvar a, a in LB(nv) ? Is this optimal?  *)
     if not (List.memq pv nv.lower.flexvars) then begin
       fv_set_lower ~changes nv (join_flexvars nv.lower [pv]);
       (* FIXME: maybe flex_cons_upper should return level? TOCTOU otherwise *)
       (* FIXME: ordering of side-effects here *)
       hoist_flex ~changes env nv.level pv;
       assert (Env_level.extends pv.level nv.level);
       subtype_flex_cons ~error ~changes env pv upper;
       ()
     end

and subtype_flex_cons ~error ~changes env pv cn =
  let cp = ensure_upper_matches ~error ~changes env pv (map_ctor_rig id ignore cn) in
  subtype_cons ~error
    ~neg:(fun _ () -> () (* already done in ensure_upper_matches *))
    ~pos:(subtype_flex_flex ~error ~changes env)
    cp cn.cons;
  ()

(* Ensure pv has a UBcons upper bound whose head is below a given ctor.
   Returns the constructed upper bound. *)
and ensure_upper_matches ~error ~changes env (pv : flexvar) (cn : (flex_lower_bound, unit) ctor_ty) : (unit, flexvar) cons_head =
  let cb = flex_cons_upper ~changes env pv in
  let cons =
    meet_cons
      ~nleft:id
      ~nright:(fun b -> join_lower ~changes env pv.level bottom b) (* FIXME bad hoist fn *)
      ~nboth:(fun a b -> join_lower ~changes env pv.level a b)
      ~pleft:id
      ~pright:(fun _ -> fresh_flexvar pv.level)
      ~pboth:(fun v _ -> v)
      cb.cons cn.cons in

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

  (* should be true by absorption law *)
  assert (map_head ignore ignore cn.cons = map_head ignore ignore cn');

  (* Dragons. *)
  (* FIUATT: should this call spec_sub unconditionally? Probably not. *)
  let spec_sub rv c =
    (* FIXME can speculative subtyping screw things up? Probably...
       The speculation seems unreliable, as whether it gets done must surely
       depend on constraint resolution order (due to width subtyping).
       So any changes we make during speculation are suspect. *)
    (* FIXME: Write more tests that actually observe weirdness here (tricky...) *)
    (* FIXME: I think this interacts especially badly with the hack
       that expands rigid variable upper bounds to flexvars. Or maybe it's fine? *)
    let error _ = raise Exit in
    let temp_changes = ref [] in
    let rb = env_rigid_bound env rv in
    match subtype_ctor_rig ~error ~changes:temp_changes env rb c with
    (* FIXME: Is this even order-independent? *)
    (* FIXME: this needs to be able to handle rigid bounds properly *)
    | () -> commit ~changes !temp_changes; true
    (*| () -> revert !temp_changes; !temp_changes = [] FIXME: is this worse? *)
    | exception Exit -> revert !temp_changes; false in
  let cbrig =
    cb.rigvars |> List.filter (fun vb ->
      if contains_rigvar vb cn.rigvars then true
      else spec_sub vb {cn with cons = cn'}) in
  let cnrig =
    cn.rigvars |> List.filter (fun vn ->
      if contains_rigvar vn cb.rigvars then false (* already included *)
      else if not (Env_level.extends vn.level pv.level) then false (* scope escape *)
      else spec_sub vn cb) in

  if cnrig = [] then begin
    let bound = { cons ; rigvars = cbrig } in
    if fv_maybe_set_upper ~changes pv (UBcons bound) then begin
      (* FIXME is this all still wf, despite hoisting? *)
      subtype_t_cons ~error ~changes env pv.lower bound;
      wf_ptyp env (Tsimple (flexlb_fv pv));
    end;
    map_head ignore id bound.cons
  end else begin
    (* Extremely tricky case.
       We had LB <= pv <= UB, but we've just decided to add rigvar(s) a to UB,
       on the basis that a <= UB already, so UB = UB | a and so adding a to the
       upper bound doesn't actually change anything.
       However, some variables in UB might be constrained from below (by LB),
       and some of these constraint might arise from approximations of rigvars in LB.
       These might no longer be necessary: if a is in LB, then a <= UB|a can be
       discharged directly without needing to constrain UB from below.
       So, if UB is growing rigvars, we freshen its matchable variables and compare
       again with LB. This may cause some variables in UB to be less constrained. *)
    (* FIXME: do I also need to freshen the contravariant parts? Something's weird here.
       Probably observable with a fiddly reflexivity example, fuzz it. *)
    let cons = map_head id (fresh_below_var pv.level) cons in
    let bound = { cons; rigvars = cbrig @ cnrig } in
    fv_set_upper ~changes pv (UBcons bound);
    subtype_t_cons ~error ~changes env pv.lower bound;
    wf_ptyp env (Tsimple (flexlb_fv pv));
    map_head ignore id bound.cons
  end


and subtype_cons_flex ~error ~changes env (cp : (flexvar, flex_lower_bound) ctor_ty) (nv : flexvar) =
  match cp with
  | { cons = Bot; rigvars = [] } ->
     (* avoid even calling flex_cons_upper in the trivial case *)
     ()
  | cp ->
     let bound = flex_cons_upper ~changes env nv in
     let lower = join_ctor ~changes env nv.level nv.lower cp in
     (* FIXME: should it be enough to compare cp instead of nv.lower? *)
     (* Printf.printf "lower bound of %a: %a --> %a\n" pp_flexvar nv pp_flexlb nv.lower pp_flexlb lower; *)
     if fv_maybe_set_lower ~changes nv lower then
       subtype_t_cons ~error ~changes env lower bound

and join_ctor ~changes env level lower cp =
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
       ~pright:(fun x -> join_lower ~changes env level bottom x)
       ~pboth:(fun x y -> join_lower ~changes env level x y)
       lower.ctor.cons cp.cons in
  (* FIXME: Top case of rigvars? check. *)
  List.fold_left (fun c rv ->
    if contains_rigvar rv c.ctor.rigvars then c
    else if Env_level.extends rv.level level then begin
      { c with ctor = { c.ctor with rigvars = c.ctor.rigvars @ [rv] } }
    end else
      join_ctor ~changes env level c (env_rigid_bound env rv))
    { ctor = {cons; rigvars = lower.ctor.rigvars }; flexvars = lower.flexvars}  cp.rigvars

and join_lower ~changes env level lower {ctor; flexvars} =
  let ctor = join_ctor ~changes env level lower ctor in
  List.iter (hoist_flex ~changes env level) flexvars;
  let lb = join_flexvars ctor flexvars in
  (* wf_flex_lower_bound ~seen:(Hashtbl.create 10) env level lower; *)
  lb


and hoist_flex ~changes env level v =
  if Env_level.extends v.level level then ()
  else match v.upper with
    | UBnone ->
       fv_set_level ~changes v level
    | UBvar v' when Env_level.extends v'.level level ->
       fv_set_level ~changes v level
    | _ ->
       let cn = flex_cons_upper ~changes env v in
       (* FIXME hoist vs. copy differs slightly for contravariant components.
          Does this matter? *)
       if Env_level.extends v.level level then
         intfail "everything's fine, but hitting this case is impressive"
       else begin
         fv_set_level ~changes v level;
         fv_set_upper ~changes v
            (UBcons (map_ctor_rig (join_lower ~changes env level bottom) (fun v -> hoist_flex ~changes env level v; v) cn));
         hoist_lower ~changes env level v.lower;
         (* FIXME hoisting: recheck *)
       end

and hoist_lower ~changes env level {ctor;flexvars} =
  map_ctor_rig (hoist_flex ~changes env level) (hoist_lower ~changes env level) ctor |> ignore;
  List.iter (hoist_flex ~changes env level) flexvars;
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
     join_flexvars (simple_ptyp fv.level t) [fv]
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
    subtype_t_cons ~error:noerror ~changes:(ref []) env (flexlb_fv fv) b
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
     subtype_flex_cons ~error:noerror ~changes:(ref []) env fv {cons;rigvars=[]};
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
     subtype_t_var ~error ~changes:(ref []) env (approx_ptyp env p) (approx_ntyp env (Tcons cn))
  | p, n -> subtype_t_var ~error ~changes:(ref []) env (approx_ptyp env p) (approx_ntyp env n); ()


(* FIXME: not ideal, probably copies too many vars *)
let join_simple env lvl p q =
  let r = bottom in
  let r = join_lower ~changes:(ref []) env lvl r p in
  let r = join_lower ~changes:(ref []) env lvl r q in
  r

(* FIXME: rank1 joins maybe?
   FIXME: keep types as Tcons if possible? Better inference. Can this matter? *)
let join_ptyp env (p : ptyp) (q : ptyp) : ptyp =
  Tsimple (join_simple env (env_level env) (approx_ptyp env p) (approx_ptyp env q))

let rec match_simple_typ ~error ~changes env lvl (p : flex_lower_bound) (head : (flexvar, flex_lower_bound ref) cons_head) =
  let {ctor = {cons; rigvars}; flexvars} = p in
  subtype_cons ~error cons head
    ~neg:(subtype_flex_flex ~error ~changes env) (* FIXME test this *)
    ~pos:(fun p r -> r := join_lower ~changes env lvl !r p);
  rigvars |> List.iter (fun rv ->
    match_simple_typ ~error ~changes env lvl {ctor=env_rigid_bound env rv;flexvars=[]} head);
  flexvars |> List.iter (fun fv ->
    let mhead = map_head flexlb_fv ignore head in
    let m = ensure_upper_matches ~error ~changes:(ref []) env fv {cons=mhead;rigvars=[]} in
    subtype_cons ~error:noerror m head
      ~neg:(fun _t () -> () (*already filled*))
      (* FIXME levels: fine as long as lvl = env_level env? Enforce? *)
      ~pos:(fun v r -> r := join_flexvars !r [v]));
  ()

(*
     let {ctor; flexvars} = approx_ptyp env t in
     wf_ptyp env p;
     let head =
       map_head
         (fun iv -> let v = fresh_flexvar lvl in
                    Ivar.put iv (Tsimple v);
                    flexlb_fv v)
         ignore
         orig_head in
     let changes = ref [] in
     subtype_cons ~error
       ~neg:(fun fv v -> subtype_flex_flex ~error ~changes env fv v)
       ~pos:(fun t () -> match_join env v t) ctor head
*)
     (* FIXME: unify with subtype_flex_cons? *)


let rec match_typ ~error env lvl (p : ptyp) (head : (ntyp Ivar.put, ptyp Ivar.put) cons_head) =
  wf_ptyp env p;
  match p with
  | Tcons c ->
     subtype_cons ~error ~neg:(fun v t -> Ivar.put v t) ~pos:(fun t v -> Ivar.put v t) c head
(* FIXME unneeded, approx_ptyp works? Nah, predicativity bad.  | Tpoly _ -> unimp "instantiate on poly match" *)
  | Tpoly {vars; body} ->
     let body = instantiate_flex env vars body in
     match_typ ~error env lvl body head
  | t ->
     let shead = map_head (fun _ -> fresh_flexvar lvl) (fun _ -> ref bottom) head in
     let changes = ref [] in
     match_simple_typ ~error ~changes env lvl (approx_ptyp env t) shead;
     subtype_cons ~error:noerror shead head
       ~neg:(fun v fv -> Ivar.put v (Tsimple fv))
       ~pos:(fun t v -> Ivar.put v (Tsimple !t));
     wf_ptyp env p;
     ()






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

let rec expand visit ~changes env level (p : flex_lower_bound) =
  let ctor = map_ctor_rig (expand_fv_neg visit ~changes env level) (expand visit ~changes env level) p.ctor in
  let flexvars = p.flexvars in
  flexvars |> List.iter (fun pv ->
    (* FIXME kinda quadratic *)
    (* FIXME: contravariant hoisting? Curried choose type? *)
    hoist_lower ~changes env pv.level p;
    if Env_level.equal pv.level level && begin_visit_pos visit pv then begin
      ignore (flex_cons_upper ~changes env pv); (* ensure upper not UBvar *)
      let lower = expand visit ~changes env level pv.lower in
      let _:bool = fv_maybe_set_lower ~changes pv lower in
      end_visit_pos visit pv
    end);
  List.fold_left (fun p v -> join_lower ~changes env level p v.lower) { ctor; flexvars } flexvars

and expand_fv_neg visit ~changes env level nv =
  if Env_level.equal nv.level level && begin_visit_neg visit nv then begin
    begin match nv.upper with
    | UBnone -> ()
    | UBvar v -> ignore (expand_fv_neg visit ~changes env level v)
    | UBcons cn ->
       let upper = UBcons (map_ctor_rig (expand visit ~changes env level) (expand_fv_neg visit ~changes env level) cn) in
       let _:bool = fv_maybe_set_upper ~changes nv upper in
       ()
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


(* FIXME dodgy as fuck tvjoin *)
let tcons {cons;rigvars} =
  List.fold_left (fun c r -> Tvjoin (c, Vrigid r)) (Tcons cons) rigvars

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
      Some (Vbound {index; var = substn_bvar visit bvars level ~index pv})
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
                     var = substn_bvar visit bvars level ~index nv })
    else substn_upper visit bvars level ~index nv.upper
  end else begin
    Tvar (Vflex nv)
  end

and substn_upper visit bvars level ~index = function
  | UBvar v -> substn_fv_neg visit bvars level ~index v
  | UBnone -> Tcons Top
  | UBcons {cons;rigvars} ->
     let cons = map_head (substn visit bvars level ~index) (substn_fv_neg visit bvars level ~index) cons in
     let rigvars_gen, rigvars_keep = List.partition (fun (rv:rigvar) -> Env_level.equal rv.level level) rigvars in
     (* Drop rigvars_gen if needed to avoid contravariant joins. *)
     match cons, rigvars_keep, rigvars_gen with
     | Bot, [], [v] -> assert (Vector.get bvars v.var = Gen_rigid v); Tvar (Vbound {index; var=v.var})
     | cons, rigvars, _ -> tcons { cons; rigvars } (* FIXME sorting? tcons? *)


(* FIXME!!: gen constraints. What can upper bounds be? *)
and substn_bvar visit bvars level ~index fv =
  assert (is_visited_neg visit fv && is_visited_pos visit fv);
  if fv.bound_var <> -1 then fv.bound_var else begin
    let r = ref (Tcons Top) in
    let n = Vector.push bvars (Gen_flex (fv, r)) in
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
  | Tvar (Vbound v) -> Tvar (Vbound v)
  | Tvjoin (t, Vbound v) ->
     (intfail "tricky case hit! (delete this)" : unit);
     Tvjoin (substn_ntyp visit bvars level ~index t, Vbound v)

  | Tvjoin (_, (Vflex _ | Vrigid _)) | Tvar (Vflex _ | Vrigid _) as n ->
     (* must be locally closed since inside tvjoin flex/rigid *)
     substn_upper visit bvars level ~index (simple_ntyp level n)

  | Tpoly {vars;body} ->
     let index = index + 1 in
     let vars = IArray.map (fun (s,t) -> s, substn_ptyp visit bvars level ~index t) vars in
     Tpoly {vars; body}
