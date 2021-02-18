open Tuple_fields
open Typedefs

exception Internal of string
let intfail fmt =
  Printf.ksprintf (fun s -> raise (Internal s)) fmt

let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)

type conflict_reason =
  | Incompatible
  | Missing of field_name
  | Extra of [`Fields|`Named of field_name]

let id x = x

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
  | _,_ -> error Incompatible

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


let styp_equal a b =
  (a = b) (* FIXME FIXME very wrong for flexvars *)

(* Check whether ty = j | ..., modulo some identities on | (but not looking under ctors) *)
let rec contains_joinand j ty =
  match j with
  | Sjoin (a, b) ->
     contains_joinand a ty && contains_joinand b ty
  | j ->
     match ty with
     | Sjoin (a, b) -> contains_joinand j a || contains_joinand j b
     | ty -> styp_equal j ty

(* FIXME: maybe also do joinand checks? *)
(* FIXME: exact spec here - not quite symmetric *)
let rec sjoin a b =
  match a, b with
  | a, Sjoin(b1, b2) -> sjoin (sjoin a b1) b2
  | Scons Top, _ | _, Scons Top -> Scons Top
  | Scons Bot, x | x, Scons Bot -> x
  | a, b when contains_joinand b a -> a
  | a, b -> Sjoin (a, b)

let contains_rigvar (v : rigvar) vs =
  List.exists (fun rv -> rv = v) vs

let contains_var (v : styp_var) vs =
  List.exists (fun v' -> v = v') vs

(*
let join_var (fb : flex_lower_bound) v =
  match v with
  | Vbound _ -> failwith "unexpected Vbound"
  | v ->
     if contains_var v fb.vars then fb
     else { fb with vars = v :: fb.vars }
*)

(* There are two ways to represent a constraint α ≤ β between two flexible variables.
   (I). Make the upper bound of α be UBvar β. (Ensure also that LB(β) contains LB(α))
   (II). Make the lower bound of β contain α. (Ensure also that UB(α) contains UB(β)) *)

(*
let rec flexvar_cons_bound (fv : flexvar) =
  match fv.upper with
  | UBnone ->
     (* switch to repr (II), to prevent this ever becoming UBvar *)
     let triv = { cons = Top; rigvars = [] } in
     fv.upper <- UBcons triv;
     triv
  | UBcons c -> c
  | UBvar v ->
     (* Switch to representation (II) *)
     assert (Env_level.equal fv.level v.level); (* FIXME not true! should hoist here *)
     v.lower <- join_var v.lower (Vflex fv);
     fv.upper <- v.upper;
     (* May recurse several times. FIXME: how do we avoid cycles? *)
     flexvar_cons_bound fv

let classify_styp_neg (n : styp) =
  match n with
  | Svar Vflex nv -> UBvar nv
  | n ->
     let rec collect = function
       | Svar (Vbound _ | Vflex _) -> assert false
       | Scons cons -> { cons; rigvars = [] }
       | Svar Vrigid v -> { cons = Bot; rigvars = [v] }
       | Sjoin (a, b) ->
          match collect a, collect b with
          | { cons = Bot; rigvars = v1 }, { cons; rigvars = v2 }
          | { cons; rigvars = v1 }, { cons = Bot; rigvars = v2 } ->
             { cons; rigvars = v1 @ v2 }
          | _ -> assert false in
     UBcons (collect n)
*)



let noerror _ = failwith "subtyping error should not be possible here!"

let bottom = {ctor={cons=Bot;rigvars=[]};flexvars=[]}

(*
 * Core subtyping functions
 *)
(* FIXME hoisting is absent here *)

let rec subtype_t_var ~error ~changed env (p : flex_lower_bound) (nv : flexvar) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_flex ~error ~changed env pv nv);
  subtype_cons_flex ~error ~changed env p.ctor nv

and subtype_t_cons ~error ~changed env (p : flex_lower_bound) (cn : (flex_lower_bound, flexvar) ctor_ty) =
  p.flexvars |> List.iter (fun pv -> subtype_flex_cons ~error ~changed env pv cn);
  p.ctor.rigvars |> List.iter (fun pv ->
    if cn.cons = Top || contains_rigvar pv cn.rigvars then ()
    else subtype_t_cons ~error ~changed env (env_rigid_bound env pv.level pv.var) cn);
  subtype_cons ~error
    ~neg:(subtype_t_var ~error ~changed env)
    ~pos:(subtype_t_var ~error ~changed env)
    p.ctor.cons cn.cons

and subtype_flex_flex ~error ~changed env (pv : flexvar) (nv : flexvar) =
  match pv.upper with
  | _ when List.memq pv nv.lower.flexvars -> ()
  | UBvar nv' when nv == nv' -> ()
  | UBnone when Env_level.equal pv.level nv.level ->
     (* FIXME: is the level check needed? *)
     changed := true;
     pv.upper <- UBvar nv; (* FIXME: can this make a cycle? *)
     subtype_t_var ~error ~changed env pv.lower nv
  | _ ->
     changed := true;
     (* FIXME rectypes support affected by ordering here *)
     (* FIXME hoisting *)
     nv.lower <- join_flexvars ~changed env nv.level nv.lower [pv];
     let bound = flex_cons_upper ~changed env nv in
     subtype_flex_cons ~error ~changed env pv bound

and flex_cons_upper ~changed env (fv : flexvar) : (flex_lower_bound, flexvar) ctor_ty =
  match fv.upper with
  | UBcons c -> c
  | UBnone ->
     let triv = { cons = Top; rigvars = [] } in
     changed := true;
     fv.upper <- UBcons triv;
     triv
  | UBvar v ->
     v.lower <- join_flexvars ~changed env v.level v.lower [fv];
     let upper = flex_cons_upper ~changed env v in
     (* To preserve matchability, need to freshen the strictly covariant variables in pv.upper. *)
     (* FIXME: fv.level? Can that change during subtype_flex_flex because hoisting? *)
     let upper = 
       map_ctor_rig
         id
         (fun v -> let v' = fresh_flexvar fv.level in
                   subtype_flex_flex ~error:noerror ~changed env v' v; v') upper in
     fv.upper <- UBcons upper;
     upper

and subtype_flex_cons ~error ~changed env pv cn =
  let cp = ensure_upper_matches ~error ~changed env pv (map_ctor_rig id ignore cn) in
  (* FIXME: duplicate rigvars code from subtype_t_cons *)
  (* FIXME: is the rigvars logic (here/subtype_t_cons/ensure_upper_matches) actually correct? *)
  cp.rigvars |> List.iter (fun pv ->
    if cn.cons = Top || contains_rigvar pv cn.rigvars then ()
    else subtype_t_cons ~error ~changed env (env_rigid_bound env pv.level pv.var) cn);
  subtype_cons ~error
    ~neg:(fun _ () -> () (* already done in ensure_upper_matches *))
    ~pos:(subtype_flex_flex ~error ~changed env)
    cp.cons cn.cons

(* Ensure pv has a UBcons upper bound whose head is below a given ctor.
   Returns the constructed upper bound.
   FIXME: poly rather than unit for cn's type *)
and ensure_upper_matches ~error ~changed env (pv : flexvar) (cn : (flex_lower_bound, unit) ctor_ty) : (unit, flexvar) ctor_ty =
  let cp = flex_cons_upper ~changed env pv in
  let changed' = ref false in
  let cons =
    meet_cons
      ~nleft:id
      ~nright:id
      ~nboth:(fun a b -> join_lower ~changed:changed' env pv.level a b)
      ~pleft:id
      ~pright:(fun _ -> fresh_flexvar pv.level)
      ~pboth:(fun v _ -> v)
      cp.cons cn.cons in
  (* FIXME: there are better ways to compute this *)
  if (map_head (fun _ -> ()) (fun _ -> ()) cp.cons <> map_head (fun _ -> ()) (fun _ -> ()) cons)
   then changed' := true;
  let rigvars =
    match cp.cons, cn.cons with
    | _, Top -> cp.rigvars
    | Top, _ ->
       assert (!changed'); (* Top meet not-Top = not-Top *)
       List.filter (fun (rv : rigvar) -> Env_level.extends rv.level pv.level) cn.rigvars
    | _, _ ->
       match List.partition (fun rv -> contains_rigvar rv cn.rigvars) cp.rigvars with
       | [], inter -> inter
       | _extra, inter -> changed' := true; inter in
  assert (!changed' || cp = {cons; rigvars}); (* FIXME poly eq *)
  if !changed' then begin
    changed := true;
    let bound = { cons; rigvars } in
    pv.upper <- UBcons bound;
    subtype_t_cons ~error ~changed env pv.lower bound
  end;
  { cons = map_head ignore id cons; rigvars }

and subtype_cons_flex ~error ~changed env (cp : (flexvar, flex_lower_bound) ctor_ty) (nv : flexvar) =
  let changed' = ref false in
  nv.lower <- join_ctor ~changed:changed' env nv.level nv.lower cp;
  if !changed' then begin
    changed := true;
    let bound = flex_cons_upper ~changed env nv in
    subtype_t_cons ~error ~changed env nv.lower bound
  end

and join_flexvars ~changed env level lower vs =
  ignore env; ignore level; (* FIXME hoisting! *)
  if lower.ctor.cons = Top then lower
  else
    match List.filter (fun v -> not (List.memq v lower.flexvars)) vs with
    | [] -> lower
    | vs -> changed := true; { lower with flexvars = lower.flexvars @ vs }

and join_ctor ~changed env level lower cp =
  let cons =
    join_cons
       ~nleft:id
       ~nright:(fun y -> let v = fresh_flexvar level in subtype_flex_flex ~error:noerror ~changed env v y; v)
       ~nboth:(fun x y -> subtype_flex_flex ~error:noerror ~changed env x y; x)
       ~pleft:id
       (* NB: pright is not id, because we need fresh variables for contravariant parts,
          to preserve matchability *)
       ~pright:(fun x -> join_lower ~changed env level bottom x)
       ~pboth:(fun x y -> join_lower ~changed env level x y)
       lower.ctor.cons cp.cons in
  if (map_head ignore ignore lower.ctor.cons <> map_head ignore ignore cons) then changed := true;
  let rigvars =
    match List.filter (fun v -> not (contains_rigvar v lower.ctor.rigvars)) cp.rigvars with
    | [] -> lower.ctor.rigvars
    | rvs -> changed := true; rvs in
  { lower with ctor = { cons; rigvars } }

and join_lower ~changed env level lower p =
  join_flexvars ~changed env level (join_ctor ~changed env level lower p.ctor) p.flexvars







(* slightly higher level functions operating on styps
   very incomplete atm, just enough to run tests *)

let subtype ~error ~changed env (p : flex_lower_bound) (n : styp_neg) =
  match n with
  | UBnone -> ()
  | UBvar nv -> subtype_t_var ~error ~changed env p nv
  | UBcons cn -> subtype_t_cons ~error ~changed env p cn


let rec lower_of_styp = function
  | Sjoin _ -> failwith "unimp"
  | Svar (Vflex fv) -> { ctor= { cons = Bot; rigvars = [] }; flexvars = [fv] }
  | Svar (Vrigid rv) -> { ctor = { cons = Bot; rigvars = [rv] }; flexvars = [] }
  | Svar (Vbound _) -> assert false
  | Scons cons ->
     let upper = function (Svar (Vflex fv)) -> fv | _ -> failwith "unimp" in
     { ctor = { cons = map_head upper lower_of_styp cons; rigvars = []}; flexvars=  [] }


let flexlb_fv fv = { ctor = { cons = Bot; rigvars = [] }; flexvars = [fv] }


let upper_of_styp = function
  | Svar (Vflex fv) -> UBvar fv
  | Scons cons ->
     let ngetfv = function Svar (Vflex fv) -> flexlb_fv fv | _ -> failwith "unimp" in
     let pgetfv = function Svar (Vflex fv) -> fv | _ -> failwith "unimp" in
     UBcons { cons = map_head ngetfv pgetfv cons;  rigvars = [] }
  | _ -> failwith "unimp"

let subtype_styp ~error env a b =
  let a = lower_of_styp a in
  let b = upper_of_styp b in
  subtype ~error ~changed:(ref false) env a b;
  let changed = ref false in
  subtype ~error ~changed env a b;
  assert (not !changed)


let match_styp ~error env p orig_head =
  let fv = match p with Svar (Vflex fv) -> fv | _ -> failwith "unimp" in
  let head =
    map_head
      (fun iv -> let v = fresh_flexvar fv.level in
                 Ivar.put iv (styp_flexvar v);
                 flexlb_fv v)
      ignore
      orig_head in
  let m = ensure_upper_matches ~error ~changed:(ref false) env fv {cons=head;rigvars=[]} in
  subtype_cons ~error:noerror
     ~neg:(fun _t () -> () (*already filled*))
     ~pos:(fun p' t' -> Ivar.put t' (styp_flexvar p'))
     m.cons orig_head












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


let rec expand visit ~changed env level (p : flex_lower_bound) =
  let ctor = map_ctor_rig (expand_fv_neg visit ~changed env level) (expand visit ~changed env level) p.ctor in
  let flexvars = p.flexvars in
  flexvars |> List.iter (fun pv ->
    if begin_visit_pos visit pv then begin
      pv.lower <- expand visit ~changed env level pv.lower;
      end_visit_pos visit pv
    end);
  List.fold_left (fun p v -> join_lower ~changed env level p v.lower) { ctor; flexvars } flexvars

and expand_fv_neg visit ~changed env level nv =
  if begin_visit_neg visit nv then begin
    begin match nv.upper with
    | UBnone -> ()
    | UBvar v -> ignore (expand_fv_neg visit ~changed env level v)
    | UBcons cn ->
       nv.upper <- UBcons (map_ctor_rig (expand visit ~changed env level) (expand_fv_neg visit ~changed env level) cn)
    end;
    end_visit_neg visit nv
  end;
  nv



let is_visited_pos visit fv =
  assert (fv.pos_visit_count land 1 = 0);
  fv.pos_visit_count = visit

let is_visited_neg visit fv =
  assert (fv.neg_visit_count land 1 = 0);
  fv.neg_visit_count = visit

let rec substn visit (p : flex_lower_bound) =
  let ctor = map_ctor_rig (substn_fv_neg visit) (substn visit) p.ctor in
  let flexvars = p.flexvars |> List.filter (fun pv ->
    assert (is_visited_pos visit pv); is_visited_neg visit pv) in
  { ctor; flexvars }

and substn_fv_neg visit nv =
  assert (is_visited_neg visit nv);
  if is_visited_pos visit nv then nv
  else match nv.upper with
  | UBvar v -> substn_fv_neg visit v
  | _ -> nv (* hack, kinda wrong *)
  





























































(*


(* FIXME: why do match_bound and update_lower_bound look so different? *)

let match_bound (pb : _ ctor_rig) level (bound : _ ctor_rig) =
  let cons = meet_cons
               ~left:(fun v -> v)
               ~right:(fun _ -> fresh_flexvar level)
               ~both:(fun v _ -> v) pb.cons bound.cons in
  let rigvars =
    match pb.cons, bound.cons with
    | Top, _ ->
       List.filter (fun rv -> Env_level.extends rv.level level) bound.rigvars
    | _, Top -> pb.rigvars
    | _, _ ->
       pb.rigvars |> List.filter (fun rv -> contains_rigvar rv bound.rigvars) in
  { cons; rigvars }

(* FIXME: get rid of this *)
let rec styp_of_flex_lower_bound (p : flex_lower_bound) =
  let cons = map_head styp_flexvar styp_of_flex_lower_bound p.cons in
  List.fold_left (fun a b -> sjoin a (Svar b)) (Scons cons) p.vars


(* (!) *)
(* Compute lower ⊔ p, preserving matchability of lower *)
let rec update_lower_bound_fb env level (lower : flex_lower_bound) (p : flex_lower_bound) =
  let vars = lower.vars @ List.filter (fun v -> not (contains_var v lower.vars)) p.vars in
  let cons = join_cons
       ~nleft:id
       ~nright:(fun y -> let v = fresh_flexvar level in subtype_styp ~error:noerror env (Svar (Vflex v)) (Svar (Vflex y)); v)
       ~nboth:(fun x y -> subtype_styp ~error:noerror env (Svar (Vflex x)) (Svar (Vflex y)); x)
       ~pleft:id
       (* NB: pright is not id, because we need fresh variables for contravariant parts,
          to preserve matchability *)
       ~pright:(fun x -> update_lower_bound_fb env level {cons=Bot;vars=[]} x)
       ~pboth:(fun x y -> update_lower_bound_fb env level x y)
       lower.cons p.cons in
  { cons; vars }


(* FIXME del *)
and update_lower_bound env (lower : flex_lower_bound) level (p : styp) =
  match p with
  | Sjoin (p, q) -> update_lower_bound env (update_lower_bound env lower level p) level q
  | Svar a ->
     begin match a with
     | Vflex fv ->
        (* fv is constrained from above, make sure it is not UBvar *)
        (* FIXME: check if the equivalent happens in contravariant parts of negative bounds *)
        (* BUG: this is wrong.
           race between the mutation occurring in flexvar_cons_bound,
           and the computation of join_var here.
           in nv.lower <- update_lower_bound env nv.lower nv.level p,
           I think we can lose an update to nv.lower (esp. w/ nested UBvars) *)
        ignore (flexvar_cons_bound fv)
     | _ -> ()
     end;
     join_var lower a
  | Scons cons ->
     let cons = join_cons
       ~nleft:id
       ~nright:(fun y -> let v = fresh_flexvar level in subtype_styp ~error:noerror env (Svar (Vflex v)) y; v)
       ~nboth:(fun x y -> subtype_styp ~error:noerror env (Svar (Vflex x)) y; x)
       ~pleft:id
       ~pright:(fun x -> update_lower_bound env {cons=Bot;vars=[]} level x)
       ~pboth:(fun x y -> update_lower_bound env x level y)
       lower.cons cons in
     { lower with cons }

(* Constraint a <= b *)
and subtype_flex_flex ~error ~changed env (pv : flexvar) (nv : flexvar) =
  match pv.upper with
  | UBvar nv' when nv == nv' ->
     (* FIXME slightly dodgy assertion *)
     assert (styp_equal nv.lower (update_lower_bound env nv.lower nv.level (Svar (Vflex pv))))
  | UBnone when Env_level.equal pv.level nv.level ->
     (* FIXME is the level eq check needed? *)
     changed := true;
     pv.upper <- UBvar nv; (* FIXME: may make a cycle? *)
     (* FIXME nv.lower <- sjoin nv.lower lower;*)
     subtype_flex_bounds ~error ~changed env pv.lower pv.upper
  | _ ->
     (* mildly dodge, don't do it this way. Get pv into state II first *)
     nv.lower <- update_lower_bound env nv.lower nv.level (Svar (Vflex pv));
     changed asdf;
     (* FIXME ??? *)
     subtype_styp_styp_neg ~error ~changed env (Svar (Vflex pv)) (map_styp_neg styp_flexvar styp_flexvar nv.upper)


(* Constraint _ <= a *)
(* FIXME del *)
and subtype_styp_var ~error ~changed env (p : styp) (nv : flexvar) =
  let p = hoist_styp ~error ~changed env nv.level Pos p in
  match p with
  | Svar Vbound _ -> assert false (* should be locally closed *)
  | Sjoin (a, b) -> subtype_styp_var ~error ~changed env a nv; subtype_styp_var ~error ~changed env b nv
  | Svar Vflex pv -> subtype_flex_flex ~error ~changed env pv nv
  | Svar Vrigid {level; var} when not (Env_level.extends level nv.level) ->
     subtype_styp_var ~error ~changed env (env_rigid_bound env level var) nv
  | (Svar Vrigid _ | Scons _) as p ->
     nv.lower <- update_lower_bound env nv.lower nv.level p;
     changed asdf;
     subtype_styp_styp_neg ~error env p (map_styp_neg styp_flexvar styp_flexvar nv.upper)

(* Constraint _ <= C *)
and subtype_styp_cons ~error ~changed env (p : styp) (cn : (styp,styp) ctor_rig) =
  match p with
  | _ when cn.cons = Top -> ()
  | Sjoin (a, b) ->
     subtype_styp_cons ~error ~changed env a cn; subtype_styp_cons ~error ~changed env b cn
  | Svar pv -> subtype_var_cons ~error ~changed env pv cn
  | Scons cp -> subtype_cons_cons ~error ~changed env cp cn

(* Constraint a <= C *)
and subtype_var_cons ~error ~changed env (pv : styp_var) (cn : (styp,styp) ctor_rig) =
  match pv with
  | Vbound _ -> assert false (* should be locally closed *)
  | Vrigid pv ->
     if cn.cons = Top || contains_rigvar pv cn.rigvars then ()
     else subtype_styp_cons ~error ~changed env (env_rigid_bound env pv.level pv.var) cn
  | Vflex pv ->
     let pb = flexvar_cons_bound pv in
     let pb' = match_bound pb pv.level cn in
     pv.upper <- UBcons pb';
     changed asdf;
     subtype_flex_bounds ~error ~changed env pv.lower pv.upper;
     (* FIXME ugly *)
     pb'.rigvars |> List.iter (fun pbv -> subtype_var_cons ~error ~changed env (Vrigid pbv) cn);
     subtype_cons_cons ~error ~changed env (map_head Pos (fun _pol v -> styp_flexvar v) pb'.cons) cn

(* Constraint LB(a) <= UB(b) *)
and subtype_flex_bounds ~error ~changed env (p : flex_lower_bound) (n : (flexvar,flexvar) styp_neg) =
  match n with
  | UBnone -> ()
  | UBvar nv ->
     subtype_styp_var ~error ~changed env (styp_of_flex_lower_bound p) nv
  | UBcons n ->
     p.vars |> List.iter (fun pv ->
       subtype_var_cons ~error ~changed env pv (map_ctor_rig styp_flexvar styp_flexvar n));
     subtype_cons ~error
       ~pos:(fun pb nv -> subtype_flex_bounds ~error ~changed env pb (UBvar nv))
       ~neg:(fun nv pv -> subtype_styp_var ~error ~changed env (Svar (Vflex nv)) pv)
       p.cons n.cons

(* Constraint C <= C *)
and subtype_cons_cons ~error ~changed env cp cn =
  subtype_cons ~error ~pos:(subtype_styp ~error ~changed env) ~neg:(subtype_styp ~error ~changed env) cp cn.cons

and subtype_styp_styp_neg ~error ~changed env p = function
  | UBnone -> ()
  | UBvar nv -> subtype_styp_var ~error ~changed env p nv
  | UBcons cn -> subtype_styp_cons ~error ~changed env p cn

and subtype_styp ~error ~changed env p n =
  subtype_styp_styp_neg ~error ~changed env p (classify_styp_neg n)

(* hoist Pos = approx from above, hoist Neg = approx from below *)
and hoist_styp ~error ~changed env lvl pol (t : styp) =
  match t with
  | Sjoin (a, b) -> sjoin (hoist_styp ~error ~changed env lvl pol a) (hoist_styp ~error ~changed env lvl pol b)
  | Scons c -> Scons (map_head pol (hoist_styp ~error ~changed env lvl) c)
  | Svar Vbound _ -> assert false (* should be locally closed *)
  | Svar Vrigid {level; var} ->
     if Env_level.extends level lvl then t
     else begin
       match pol with
       | Pos -> hoist_styp ~error ~changed env lvl pol (env_rigid_bound env level var)
       | Neg -> Scons Bot
     end
  | Svar Vflex fv ->
     if Env_level.extends fv.level lvl then t
     else
       failwith "hoist: not sure what to do here"
                (*
                  changed := true
       begin match fv.upper with
       | 
       let old_upper = fv.upper in
       fv.upper <- UBcons Top;
       fv.level <- lvl;
       fv.lower <- hoist_styp ~error env lvl pol fv.lower;
       (* this is really weird *)
       subtype_styp ~error env t old_upper;
       t
                 *)

(* Find the smallest type T fitting the template t where p <= T  *)
let rec match_styp ~error env p (t : (styp Ivar.put, styp Ivar.put) cons_head) : unit =
  match p with
  | Sjoin _ -> failwith "waiting for join/meet to be implemented"
  | Scons c ->
     subtype_cons ~error ~pos:(fun p' t' -> Ivar.put t' p') ~neg:(fun t' p' -> Ivar.put t' p') c t
  | Svar Vbound _ -> assert false (* should be locally closed *)
  | Svar Vrigid {level;var} ->
     match_styp ~error env (env_rigid_bound env level var) t
  | Svar Vflex pv ->
     (* FIXME: unify with subtype_var_cons case (easy) *)
     let pb = flexvar_cons_bound pv in
     let pb' = match_bound pb pv.level {cons=t; rigvars=[]} in
     pv.upper <- UBcons pb';
     subtype_flex_bounds ~error env pv.lower pv.upper;
     subtype_cons ~error ~pos:(fun p' t' -> Ivar.put t' (styp_flexvar p')) ~neg:(fun t' p' -> Ivar.put t' (styp_flexvar p')) pb'.cons t
     

type visited_state = Unvisited | Visiting | Visited

type gen_state = {
  mutable pos : visited_state;
  mutable neg : visited_state;
}

module M = struct type flexvar_state += Gen of gen_state end

let fv_state (fv : flexvar) =
(*  assert (Env_level.equal fv.level level);*)
  match fv.state with
  | No_flexvar_state ->
     let s = { pos = Unvisited; neg = Unvisited } in
     fv.state <- M.Gen s;
     s
  | M.Gen s -> s
  | _ -> assert false


let gen env level t =

  (* I'm not convinced that this loop is right.
     update_lower_bound runs too late. *)

  (* This is totally wrong. update_lower_bound mutates everything. *)

  (* New plan: the first pass expands and computes only pos marks.
     Is it just neg marks that are wrong?
     No, I->II conversions can change expansions :( *)

  (* 

What can change during an update_lower_bound?
1. We change positively occurring variables from I to II
   (This should not happen below, as all of these come from lower bounds,
    and so should already be in form II)
2. We resolve constraints α ≤ S where α is a flexible variable whose only negative occurrence
   is in the lower bound
3. We create new flexible variables like α.

It is possible that α occurs positively elsewhere, because we could have done α ≤ β,
converted α to form II, and stored it positively in the expansion of β.
Such occurrences can arise during update_lower_bound.

α is never directly constrained from below. It occurs in a constructed bound and only used
on the LHS of constraints. Its lower bound will always be trivial.

In this particular case, all of these come from lower bounds.
In particular, the constraints in #2 will always be α ≤ β, where β is a similar variable.

Resolving constraints in #2 may cause:
2a: α to become a type I variable (α ≤ β)
2b: α to become a type II variable, constrained against UB(β)

During update_lower_bound:

  - All newly-created variables are at most negatively reachable
    (They are negatively reachable at creation but may be stomped by further joins)
    There are no new positively reachable variables


I think something weird can happen that might really require a fixpoint computation.
Here goes:
1. We have a variable a ≤ b → c
2. We have a variable p ≤ q → r
3. 


   *)


  (* Visit a positively-occurring flex variable and compute its expansion *)
  (* FIXME check level of fv *)
  let rec visit_fv_pos (fv : flexvar) =
    begin match fv.upper with
    | UBvar _ -> failwith "error: UBvar flexvar positively reachable"
    | _ -> ()
    end;
    let state = fv_state fv in
    match state.pos with
    | Visiting -> failwith "pos cycle found, rec types not implemented"
    | Visited -> ()
    | Unvisited ->
       state.pos <- Visiting;
       fv.lower <- visit_flexlb_pos fv.lower;
       state.pos <- Visited

  and visit_flexlb_pos { cons; vars } =
    (* FIXME: try to ensure that variables created during update_lower_bound get visited
       appropriately. Maybe visit again afterwards? *)
    let cons = map_head visit_neg visit_flexlb_pos cons in
    List.fold_left (fun s v ->
       let s =
         match v with
         | Vflex fv -> update_lower_bound env s level (visit_fv_pos fv; styp_of_flex_lower_bound fv.lower)
         | _ -> s in
       join_var s v) { cons; vars = [] } vars

  and visit_neg fv =
    (* remap to something that's not UBvar *)
    match fv.upper with
    | UBnone -> fv
    | UBvar fv -> visit_neg fv
    | UBcons bound ->
       let state = fv_state fv in
       match state.neg with
       | Visiting -> failwith "neg cycle found, rec types not implemented"
       | Visited -> fv
       | Unvisited ->
          state.neg <- Visiting;
          let {cons; rigvars} = bound in
          let cons = map_head (fun v -> visit_fv_pos v; v) visit_neg cons in
          fv.upper <- UBcons {cons; rigvars};
          state.neg <- Visited;
          fv
  in
  let root = fresh_flexvar level in
  subtype_styp ~error:noerror env t (styp_flexvar root);
  visit_fv_pos root;
  root

let gen_subst _env _level root =
  let rec subst_fv_pos (fv : flexvar) =
    assert ((fv_state fv).pos = Visited);
    subst_flexlb_pos (join_var fv.lower (Vflex fv))
  
  and subst_flexlb_pos { cons; vars } =
    let cons = map_head subst_fv_neg subst_flexlb_pos cons in
    let vars = List.filter (function Vflex fv -> assert ((fv_state fv).pos = Visited); (fv_state fv).neg = Visited | _ -> true) vars in
    List.fold_left (fun c v -> sjoin c (Svar v)) (Scons cons) vars

  and subst_fv_neg fv =
    if ((fv_state fv).neg <> Visited) then
      intfail "unvisted neg var %s" (flexvar_name fv);
    if (fv_state fv).pos = Visited then styp_flexvar fv
    else
      match fv.upper with
      | UBvar _ -> assert false (* should have been removed earlier *)
      | UBnone -> styp_cons Top
      | UBcons {cons;rigvars} ->
         let cons = map_head subst_fv_pos subst_fv_neg cons in
         List.fold_left (fun c v -> sjoin c (Svar (Vrigid v))) (styp_cons cons) rigvars
  in

  subst_fv_pos root
*)

(*
let gen level t =
  let module M = struct type flexvar_state += Gen of gen_state end in

  let fv_state (fv : flexvar) =
    match fv.state with
    | No_flexvar_state ->
       let s = { pos = false; neg = false; pos_expansion = None } in
       fv.state <- M.Gen s;
       s
    | M.Gen s -> s
    | _ -> assert false in
  let rec walk pol t =
    match t with
    | Svar (Vflex fv) when Env_level.equal fv.level level ->
       walk_var pol fv
    | Svar _ -> ()
    | Sjoin (a, b) -> walk pol a; walk pol b
    | Scons c ->
       ignore (map_head pol walk c)
  and walk_var pol fv =
    let fvs = fv_state fv in
    match pol with
    | Pos ->
       if fvs.pos_expansion = None then begin
         if fvs.pos then failwith "pos cycle found, not supported (yet!?)";
         fvs.pos <- true;
         fvs.pos_expansion <- Some (expand_pos [] [] [fv.lower])
       end
    | Neg ->
       if not fvs.neg then begin
         fvs.neg <- true;
         walk Neg fv.upper
       end
  in

  (* Convert a join of positive styps to canonical form:
      a join of at most one constructed type and a bunch of variables *)
  let rec canon_pos conses vars = function
    | Sjoin (a, b) :: rest ->
       canon_pos conses vars (a :: b :: rest)
    | Svar v :: rest ->
       canon_pos conses (v :: vars) rest
    | Scons c :: rest ->
       canon_pos (c :: conses) vars rest
    | [] ->
       let join_accum = join_cons ~left:(fun x -> [x]) ~right:id ~both:(fun a b -> a :: b) in
       let cons = List.fold_right join_accum conses Bot in
       let cons = map_head Pos canon cons in
       List.fold_left sjoin (Scons cons) (List.map (fun v -> Svar v) vars)

  (* Convert a meet of negative styps to canonical form:
      either a single flexible variable or a type without flexible variables *)
  and canon_neg tys =
    (*

What is C ⊓ β when β is higher up?
We should introduce γ at the level of β
and say γ ≤ C, γ ≤ β. Is that enough?

*)
       

  and canon pol tys =
    match pol with
    | Pos -> canon_pos [] [] tys
    | Neg -> asdf
  in
  walk Pos t

*)
  

(*


(* join Pos = ⊔, join Neg = ⊓ (meet) *)
let rec join pol (a : styp) (b: styp) =
  match styp_unconsv2 a b with
  | Cons2 { a; b } -> styp_cons pol (join_cons pol a b)
  | Vars2 { level; a; va; b; vb } ->
     styp_consv level (join pol a b) (vlist_union va vb)

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
  match Styp.de pol ty with
  | Cons cons ->
     Styp.mk pol (Cons (map_head pol (approx_styp env apxcache lvl) cons))
  | Free_vars { level; vars; rest } ->
     let rest = approx_styp env apxcache lvl pol rest in
     if Env_level.extends level lvl then
       (* can keep *)
       Styp.mk pol (Free_vars { level; vars; rest })
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
  match Styp.de Pos p with
  | Cons cons -> cons, []
  | Free_vars { level = lvl; rest = p; vars = vs } ->
     match env_entry_at_level env lvl with
     | Eflexible {vars=fvs;_} ->
        vs |> Intlist.to_list |> List.fold_left (fun (r, errs) (v,()) ->
          let fv = Vector.get fvs v in
          let cons = join_cons Neg fv.neg_match_cache
                       (map_head Neg (fun pol () -> styp_trivial pol) t) in
          let freshen pol t =
            match Styp.de pol t with
            | Free_vars { level; vars; rest } when is_trivial pol rest ->
               t, styp_vars (polneg pol) level vars
            | _ when is_trivial pol t ->
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
*)
