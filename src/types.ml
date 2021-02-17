open Tuple_fields
open Typedefs

exception Internal of string
let intfail s = raise (Internal s)
let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

type conflict_reason =
  | Incompatible
  | Missing of field_name
  | Extra of [`Fields|`Named of field_name]

(* FIXME: too much poly compare in this file *)
(* let (=) (x : int) (y : int) = x = y *)

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

let meet_cons ~left ~right ~both a b =
  match a, b with
  | Bot, _ | _, Bot -> Bot
  | c, Top -> map_head Neg (fun _pol v -> left v) c
  | Top, c' -> map_head Neg (fun _pol v -> right v) c'
  | Bool, Bool -> Bool
  | Int, Int -> Int
  | String, String -> String
  | (Bool|Int|String), _ | _, (Bool|Int|String) -> Bot
  | Record _, Func _ | Func _, Record _ -> Bot
  | Record c, Record c' ->
     begin match Tuple_fields.union ~left ~right ~both c c' with
     | Some r -> Record r
     | None -> Bot
     end
  | Func (args, res), Func (args', res') ->
     (* FIXME: matching isn't really needed on contravariant components.
        Simpler to do it anyway, though *)
     (* FIXME: fail here rather than assuming variadic functions?
        Could/should enforce that functions are always `Closed *)
     let args = Tuple_fields.inter ~both args args' in
     Func (args, both res res')


let map_head' neg pos = function
  | Top -> Top
  | Bot -> Bot
  | Bool -> Bool
  | Int -> Int
  | String -> String
  | Record fields -> Record (map_fields (fun _fn x -> pos x) fields)
  | Func (args, res) ->
     Func (map_fields (fun _fn x -> neg x) args, pos res)

let id x = x

let join_cons
  ~nleft ~nright ~nboth
  ~pleft ~pright ~pboth
  a b =
  match a, b with
  | Top, _ | _, Top -> Top
  | c, Bot -> map_head' nleft pleft c
  | Bot, c' -> map_head' nright pright c'
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

(* There are two ways to represent a constraint α ≤ β between two flexible variables.
   (I). Make the upper bound of α be UBvar β. (Ensure also that LB(β) contains LB(α))
   (II). Make the lower bound of β contain α. (Ensure also that UB(α) contains UB(β)) *)

let rec flexvar_cons_bound (fv : flexvar) =
  match fv.upper with
  | UBnone ->
     (* switch to repr (II), to prevent this ever becoming UBvar *)
     let triv : _ ctor_rig = { cons = Top; rigvars = [] } in
     fv.upper <- UBcons triv;
     triv
  | UBcons c -> c
  | UBvar v ->
     (* Switch to representation (II) *)
     assert (Env_level.equal fv.level v.level); (* FIXME not true! should hoist here *)
     v.lower <- { v.lower with vars = Vflex fv :: v.lower.vars }; (* FIXME: duplicate possible? *)
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


let map_ctor_rig f { cons; rigvars } = { cons = map_head Pos (fun _pol x -> f x) cons; rigvars }
let map_styp_neg f = function UBnone | UBvar _ as x -> x | UBcons c -> UBcons (map_ctor_rig f c)

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
  let cons = map_head' styp_flexvar styp_of_flex_lower_bound p.cons in
  List.fold_left (fun a b -> sjoin a (Svar b)) (Scons cons) p.vars

let noerror _ = failwith "subtyping error should not be possible here!"

(* (!) *)
(* Compute lower ⊔ p, preserving matchability of lower *)
let rec update_lower_bound env (lower : flex_lower_bound) level (p : styp) =
  match p with
  | Sjoin (p, q) -> update_lower_bound env (update_lower_bound env lower level p) level q
  | Svar (Vbound _) -> failwith "should be locally closed"
  | Svar a when contains_var a lower.vars -> lower
  | Svar ((Vrigid _) as a) -> { lower with vars = a :: lower.vars }
  | Svar ((Vflex fv) as a) ->
     (* fv is constrained from above, make sure it is not UBvar *)
     (* FIXME: check if the equivalent happens in contravariant parts of negative bounds *)
     ignore (flexvar_cons_bound fv);
     { lower with vars = a :: lower.vars }
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
     

(* Constraint _ <= a *)
and subtype_styp_var ~error env (p : styp) (nv : flexvar) =
  let p = hoist_styp ~error env nv.level Pos p in
  match p with
  | Svar Vbound _ -> assert false (* should be locally closed *)
  | Sjoin (a, b) -> subtype_styp_var ~error env a nv; subtype_styp_var ~error env b nv
  | Svar Vflex { upper = UBvar nv'; _ } when nv == nv' ->
     assert (styp_equal nv.lower (update_lower_bound env nv.lower nv.level p))
  | Svar Vflex ({ upper = UBnone; _} as pv)
     when Env_level.equal pv.level nv.level ->
     (* Flexible-flexible constraint, representation (I) works. *)
     (*nv.lower <- sjoin nv.lower lower;*)
     pv.upper <- UBvar nv; (* FIXME may make a cycle? *)
     subtype_flex_bounds ~error env pv.lower pv.upper
  | p ->
     nv.lower <- update_lower_bound env nv.lower nv.level p;
     subtype_styp_styp_neg ~error env p (map_styp_neg styp_flexvar nv.upper)

(* Constraint _ <= C *)
and subtype_styp_cons ~error env (p : styp) (cn : styp ctor_rig) =
  match p with
  | _ when cn.cons = Top -> ()
  | Sjoin (a, b) -> subtype_styp_cons ~error env a cn; subtype_styp_cons ~error env b cn
  | Svar pv -> subtype_var_cons ~error env pv cn
  | Scons cp -> subtype_cons_cons ~error env cp cn

(* Constraint a <= C *)
and subtype_var_cons ~error env (pv : styp_var) (cn : styp ctor_rig) =
  match pv with
  | Vbound _ -> assert false (* should be locally closed *)
  | Vrigid pv ->
     if cn.cons = Top || contains_rigvar pv cn.rigvars then ()
     else subtype_styp_cons ~error env (env_rigid_bound env pv.level pv.var) cn
  | Vflex pv ->
     let pb = flexvar_cons_bound pv in
     let pb' = match_bound pb pv.level cn in
     pv.upper <- UBcons pb';
     subtype_flex_bounds ~error env pv.lower pv.upper;
     (* FIXME ugly *)
     pb'.rigvars |> List.iter (fun pbv -> subtype_var_cons ~error env (Vrigid pbv) cn);
     subtype_cons_cons ~error env (map_head Pos (fun _pol v -> styp_flexvar v) pb'.cons) cn

(* Constraint LB(a) <= UB(b) *)
and subtype_flex_bounds ~error env (p : flex_lower_bound) (n : flexvar styp_neg) =
  match n with
  | UBnone -> ()
  | UBvar nv ->
     subtype_styp_var ~error env (styp_of_flex_lower_bound p) nv
  | UBcons n ->
     p.vars |> List.iter (fun pv ->
       subtype_var_cons ~error env pv (map_ctor_rig styp_flexvar n));
     subtype_cons ~error
       ~pos:(fun pb nv -> subtype_flex_bounds ~error env pb (UBvar nv))
       ~neg:(fun nv pv -> subtype_styp_var ~error env (Svar (Vflex nv)) pv)
       p.cons n.cons

(* Constraint C <= C *)
and subtype_cons_cons ~error env cp cn =
  subtype_cons ~error ~pos:(subtype_styp ~error env) ~neg:(subtype_styp ~error env) cp cn.cons

and subtype_styp_styp_neg ~error env p = function
  | UBnone -> ()
  | UBvar nv -> subtype_styp_var ~error env p nv
  | UBcons cn -> subtype_styp_cons ~error env p cn

and subtype_styp ~error env p n =
  subtype_styp_styp_neg ~error env p (classify_styp_neg n)

(* hoist Pos = approx from above, hoist Neg = approx from below *)
and hoist_styp ~error env lvl pol (t : styp) =
  match t with
  | Sjoin (a, b) -> sjoin (hoist_styp ~error env lvl pol a) (hoist_styp ~error env lvl pol b)
  | Scons c -> Scons (map_head pol (hoist_styp ~error env lvl) c)
  | Svar Vbound _ -> assert false (* should be locally closed *)
  | Svar Vrigid {level; var} ->
     if Env_level.extends level lvl then t
     else begin
       match pol with
       | Pos -> hoist_styp ~error env lvl pol (env_rigid_bound env level var)
       | Neg -> Scons Bot
     end
  | Svar Vflex fv ->
     if Env_level.extends fv.level lvl then t
     else
       failwith "not sure what to do here"
                (*
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
     (* FIXME: unify with subtype_styp_cons case (easy) *)
     let pb = flexvar_cons_bound pv in
     let pb' = match_bound pb pv.level {cons=t; rigvars=[]} in
     pv.upper <- UBcons pb';
     subtype_flex_bounds ~error env pv.lower pv.upper;
     subtype_cons ~error ~pos:(fun p' t' -> Ivar.put t' (styp_flexvar p')) ~neg:(fun t' p' -> Ivar.put t' (styp_flexvar p')) pb'.cons t
     

type pos_replacement = {
  cons : (pos_replacement,pos_replacement) cons_head;
  gen_vars : flexvar list;
  other_vars : styp_var list;
}

type gen_state = {
  mutable pos : bool;
  mutable neg : bool;
  mutable pos_expansion : pos_replacement option;
}
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
