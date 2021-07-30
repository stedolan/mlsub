(*
 * Core definitions used by the typechecker
 *)

module StrMap = Map.Make (struct type t = string let compare = compare end)

exception Internal of string
let intfail fmt =
  Format.kasprintf (fun s -> raise (Internal s)) fmt
let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

exception Unimplemented of string
let unimp fmt =
  Format.kasprintf (fun s -> raise (Unimplemented s)) fmt
let () = Printexc.register_printer (function Unimplemented s -> Some ("unimplemented: " ^ s) | _ -> None)

let id x = x

type zero = |
let never : zero -> 'a = function _ -> .

(* Immutable arrays *)
module IArray : sig
  type +'a t
  val empty : 'a t
  val make : 'a array -> 'a t
  val get : 'a t -> int -> 'a
  val length : 'a t -> int
  val of_list : 'a list -> 'a t
  val of_array : 'a array -> 'a t
  val to_list : 'a t -> 'a list
  val to_array : 'a t -> 'a array
  val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val iter : ('a -> unit) -> 'a t -> unit
  val iteri : (int -> 'a -> unit) -> 'a t -> unit
  val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val exists : ('a -> bool) -> 'a t -> bool
  val map_fold_left : ('s -> 'a -> 's * 'b) -> 's -> 'a t -> 's * 'b t
end = struct
  type +'a t = Mk : 'b array * ('b -> 'a) -> 'a t
  let acopy a = Array.map id a
  let empty = Mk ([| |], id)
  let make x = Mk (Array.map id x, id)
  let get (Mk (a, r)) i = r a.(i)
  let length (Mk (a, _r)) = Array.length a
  let of_list l = make (Array.of_list l)
  let of_array a = Mk(acopy a, id)
  let to_array (Mk (a, r)) = Array.map r a
  let to_list x = to_array x |> Array.to_list
  let map f (Mk (a, r)) = Mk (Array.init (Array.length a) (fun i -> f (r a.(i))), id)
  let mapi f (Mk (a, r)) = Mk (Array.init (Array.length a) (fun i -> f i (r a.(i))), id)
  let iteri f (Mk (a, ra)) =
    Array.iteri (fun i x -> f i (ra x)) a
  let iter2 f (Mk (a, ra)) (Mk (b, rb)) =
    Array.iter2 (fun a b -> f (ra a) (rb b)) a b
  let iter f (Mk (a, r)) = Array.iter (fun x -> f (r x)) a
  let exists f (Mk (a, r)) = Array.exists (fun x -> f (r x)) a
  let map_fold_left f s (Mk (a, r)) =
    let st = ref s in
    let out = ref [| |] in
    for i = 0 to Array.length a - 1 do
      let x = a.(i) in
      let s, b = f !st (r x) in
      let out =
        match !out with
        | [| |] -> out := Array.make (Array.length a) b; !out
        | o -> o in
      out.(i) <- b;
      st := s
    done;
    !st, of_array !out
end
type 'a iarray = 'a IArray.t

open Tuple_fields

(* Head type constructors. These do not bind type variables. *)
type (+'neg, +'pos) cons_head =
  | Top
  | Bot
  (* FIXME: maybe delete these once abstypes exist? *)
  | Bool
  | Int
  | String
  | Record of 'pos tuple_fields
  | Func of 'neg tuple_fields * 'pos

let map_head neg pos = function
  | Top -> Top
  | Bot -> Bot
  | Bool -> Bool
  | Int -> Int
  | String -> String
  | Record fields -> Record (map_fields (fun _fn x -> pos x) fields)
  | Func (args, res) ->
     Func (map_fields (fun _fn x -> neg x) args, pos res)

let equal_cons neg pos p q =
  match p, q with
  | Top, Top -> true
  | Bot, Bot -> true
  | Bool, Bool -> true
  | Int, Int -> true
  | String, String -> true
  | Record p, Record q ->
     equal_fields pos p q
  | Func (pa, pr), Func (qa, qr) ->
     equal_fields neg pa qa && pos pr qr
  | (Top|Bot|Bool|Int|String|Record _|Func _), _ -> false

let equal_lists f p q =
  try List.for_all2 f p q
  with Invalid_argument _ -> false

let rec compare_lists f p q =
  match p, q with
  | [], [] -> 0
  | p::ps, q::qs ->
     let cmp = f p q in
     if cmp = 0 then compare_lists f ps qs else cmp
  | [], _::_ -> -1
  | _::_, [] -> 1

module Env_level : sig
  type t

  val initial : t
  val extend : t -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val extends : t -> t -> bool

  val to_int : t -> int
end = struct
  (* Not actually mutable, but marking it as such
     makes physical equality work *)
  type t =
    { mutable level : int }

  let initial = { level = 0 }
  let extend { level } = { level = level + 1 }

  let compare { level=l1} {level=l2} = compare l1 l2

  let extends {level=l1} {level=l2} = l1 <= l2

  let equal l1 l2 =
    if l1.level = l2.level then
      (assert (l1 == l2); true)
    else
      false

  let to_int l = l.level
end

type env_level = Env_level.t

(* Rigid variables are immutable.
   Their bounds are stored in the environment. *)
type rigvar =
  { level: env_level;
    var: int }

let equal_rigvar (p : rigvar) (q : rigvar) =
  Env_level.equal p.level q.level && p.var = q.var

let compare_rigvar (p : rigvar) (q : rigvar) =
  (* negate: sort highest level earliest *)
  let cmp = ~- (compare (Env_level.to_int p.level) (Env_level.to_int q.level)) in
  if cmp <> 0 then cmp else
    (assert (Env_level.equal p.level q.level); compare p.var q.var)

(* Sets of rigid variables *)
module Rvset : sig
  type t
  val empty : t
  val singleton : rigvar -> Location.set -> t
  val add : t -> rigvar -> Location.set -> t
  val join : t -> t -> t

  val to_list : t -> rigvar list
  val to_list_loc : t -> (rigvar * Location.set) list

  val contains : t -> rigvar -> bool

  val is_empty : t -> bool

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val peel_level : Env_level.t -> t -> ((rigvar * Location.set) list * t)

  val filter : (rigvar -> bool) -> t -> t

  val fold : ('s -> rigvar * Location.set -> 's) -> 's -> t -> 's
end = struct
  type t = (rigvar * Location.set) list
  let empty = []
  let singleton x l = [x, l]

  let cmprv (r, _) (s, _) = compare_rigvar r s

  let add t rv l =
    (* FIXME hilarious *)
    List.sort_uniq cmprv ((rv, l) :: t)

  let to_list t = List.map fst t
  let to_list_loc t = t

  let contains t rv =
    List.exists (fun (r, _) -> equal_rigvar r rv) t

  let join t vs =
    (* FIXME *)
    List.sort_uniq cmprv (t @ vs)

  let is_empty = function [] -> true | _ -> false

  let equal a b = equal_lists (fun (r, _) (s, _) -> equal_rigvar r s) a b
  let compare a b = compare_lists cmprv a b

  let peel_level lvl xs =
    (* FIXME: since lvl is always at the start, this could be faster *)
    List.partition (fun ((rv : rigvar), _) ->
      assert (Env_level.extends rv.level lvl);
      Env_level.equal rv.level lvl) xs

  let filter p t = List.filter (fun (r, _) -> p r) t

  let fold = List.fold_left
end

type cons_locs = ((unit,unit) cons_head * Location.set) list
let mk_cons_locs loc cons =
  [map_head ignore ignore cons, Location.single loc]

(* A ctor_ty is a join of a constructed type and some rigid variables *)
type (+'neg,+'pos) ctor_ty =
  { cons: ('neg,'pos) cons_head; rigvars: Rvset.t;
    cons_locs: cons_locs }

(* FIXME: most uses of this function are probably bugs: rigvars need attention *)
let map_ctor_rig neg pos { cons; rigvars; cons_locs } =
  { cons = map_head neg pos cons; rigvars; cons_locs }



(* Temporary structure used during generalisation *)
type flexvar_gen_visit_counts = { mutable pos : int; mutable neg : int }

type flexvar_gen_status =
  | No_var_chosen
  | Computing_bound
  | Generalised of int
  | Replace_with_rigid of (rigvar * Location.set) list

type flexvar_gen =
  | Not_generalising
  | Generalising of {
      level: env_level;
      visit : flexvar_gen_visit_counts;
      mutable bound_var : flexvar_gen_status
    }


(* Flexvars are mutable but only in one direction.
     - level may decrease
     - bounds may become tighter (upper decreases, lower increases) *)
type flexvar =
  { mutable level: env_level;
    mutable upper: styp_neg list; (* strictly covariant parts are matchable *)
    mutable lower: flex_lower_bound; (* If lower is nontrivial, then upper must be UBcons. FIXME: encode this? *)
    id: int;    (* just for printing/sorting *)
    mutable gen: flexvar_gen; }

(* A well-formed negative styp is either:
     - a single flexible variable
     - a constructed type, possibly joined with some rigid variables *)
and styp_neg =
  | UBvar of flexvar
    (* Only one allowed per set of rigid variables *)
  | UBcons of (flex_lower_bound, flexvar) ctor_ty

(* Matchability constraint: the contravariant parts of a flexible variable's lower bound must be flexible variables.
   Flexible variables appearing in vars must not have UBvar upper bounds, as they are also constrained above here.
   Flexible variables appearing negatively in ctor might well have UBvar upper bounds.
 *)
and flex_lower_bound =
  { ctor: (flexvar, flex_lower_bound) ctor_ty; flexvars: flexvar list }


type typ_var =
  | Vbound of {index: int; var:int}
  | Vflex of flexvar
  | Vrigid of rigvar

type (+'neg, +'pos) typ =
  | Tsimple of 'pos
  | Tcons of cons_locs * ('neg, 'pos) cons_typ
  | Tvar of Location.set * typ_var
  | Tvjoin of ('neg, 'pos) typ * Location.set * typ_var
     (* Tvjoin(t,v): t must be well-scoped at level of var *)
  | Tpoly of {
     (* names must be distinct *)
     (* bound must be a constructed type, possibly joined with some rigid/bound vars *)
     vars : (string * ('pos, 'neg) typ) iarray;
     body : ('neg, 'pos) typ }
and (+'neg, +'pos) cons_typ = (('pos, 'neg) typ, ('neg, 'pos) typ) cons_head

type ptyp = (flexvar, flex_lower_bound) typ
type ntyp = (flex_lower_bound, flexvar) typ

type env =
  | Env_vals of { vals : ptyp SymMap.t; rest : env }
  | Env_types of { level : env_level; rig_names : int SymMap.t; rig_defns : rigvar_defn iarray; rest : env }
  | Env_nil

(* Rigid type variables. *)
and rigvar_defn = {
  (* unique among a binding group, but can shadow.
     Only used for parsing/printing: internally, referred to by index. *)
  name : string;
  (* FIXME: flex_lower_bound? Are rigid vars allowed in upper bound heads?
     FIXME: this seems very dubious *)
  upper : (flexvar, flex_lower_bound) cons_head;
}

(*
 * Equality checks (Syntactic, not subtyping-aware, ignore locations)
 *)

let equal_flexvar (p : flexvar) (q : flexvar) =
  p == q
let rec equal_flex_lower_bound (p : flex_lower_bound) (q : flex_lower_bound) =
  equal_lists equal_flexvar p.flexvars q.flexvars &&
  Rvset.equal p.ctor.rigvars q.ctor.rigvars &&
  equal_cons equal_flexvar equal_flex_lower_bound p.ctor.cons q.ctor.cons
let equal_styp_neg (p : styp_neg) (q : styp_neg) =
  match p, q with
  | UBvar pv, UBvar qv -> equal_flexvar pv qv
  | UBcons cp, UBcons cq ->
     Rvset.equal cp.rigvars cq.rigvars &&
     equal_cons equal_flex_lower_bound equal_flexvar cp.cons cq.cons
  | (UBvar _|UBcons _), _ -> false

let bottom = {ctor={cons=Bot;rigvars=Rvset.empty;cons_locs=[]};flexvars=[]}
let is_bottom t = equal_flex_lower_bound bottom t

(*
 * Flexvar mutations and backtracking log
 *)

type flexvar_change =
  | Change_expanded_mark (* hack for logging expand changes *)
  | Change_level of flexvar * env_level
  | Change_upper of flexvar * styp_neg list
  | Change_lower of flexvar * flex_lower_bound

let fv_set_level ~changes fv level =
  assert (Env_level.extends level fv.level);
  if not (Env_level.equal level fv.level) then begin
    changes := Change_level (fv, fv.level) :: !changes;
    fv.level <- level;
    (* Cancel any generalisation in progress (see expand) *)
    if fv.gen <> Not_generalising then fv.gen <- Not_generalising;
  end

let fv_set_upper ~changes fv upper =
  changes := Change_upper (fv, fv.upper) :: !changes;
  fv.upper <- upper

let fv_set_lower ~changes fv lower =
  List.iter (fun fv' -> assert (fv != fv')) lower.flexvars;
  changes := Change_lower (fv, fv.lower) :: !changes;
  fv.lower <- lower

let fv_maybe_set_lower ~changes fv lower =
  if not (equal_flex_lower_bound fv.lower lower) then
    (fv_set_lower ~changes fv lower; true)
  else false

let fv_maybe_set_upper ~changes (fv : flexvar) upper =
  if not (equal_lists equal_styp_neg fv.upper upper) then
    (fv_set_upper ~changes fv upper; true)
  else false

let revert changes =
  changes |> List.iter (function
  | Change_expanded_mark -> ()
  | Change_level (fv, level) -> fv.level <- level
  | Change_upper (fv, upper) -> fv.upper <- upper
  | Change_lower (fv, lower) -> fv.lower <- lower)

let commit ~changes rest =
  changes := rest @ !changes

(*
 * Environment ordering
 *)

let rec env_at_level env lvl =
  match env with
  | Env_vals { vals=_; rest } -> env_at_level rest lvl
  | Env_types tys when Env_level.equal tys.level lvl -> env
  | Env_types tys ->
     assert (Env_level.extends lvl tys.level); env_at_level tys.rest lvl
  | Env_nil when Env_level.equal Env_level.initial lvl -> Env_nil
  | Env_nil -> intfail "env level not found"

let env_rigid_vars env lvl =
  match env_at_level env lvl with
  | Env_types tys ->
     assert (Env_level.equal tys.level lvl); tys.rig_defns
  | _ -> intfail "env_rigid_vars"

let env_rigid_bound env (rv : rigvar) =
  (IArray.get (env_rigid_vars env rv.level) rv.var).upper

let rec env_level env =
  match env with
  | Env_types tys -> tys.level
  | Env_vals vs -> env_level vs.rest
  | Env_nil -> Env_level.initial

(* visit counters: odd = visiting, even = done *)
let fv_gen_visit_counts env fv =
  let level = env_level env in
  assert (Env_level.extends fv.level level);
  if not (Env_level.equal fv.level level) then None
  else match fv.gen with
  | Generalising g ->
     assert (Env_level.equal fv.level g.level);
     Some g.visit
  | Not_generalising ->
     let visit = { pos = 0; neg = 0 } in
     fv.gen <- Generalising { level = fv.level; visit; bound_var = No_var_chosen };
     Some visit

type visit_type = First_visit | Recursive_visit
let fv_gen_visit_pos env visit fv k =
  match fv_gen_visit_counts env fv with
  | None -> ()
  | Some v ->
     assert (v.pos <= visit);
     if v.pos = visit then () (* visited already *)
     else if v.pos = visit - 1 then k Recursive_visit
     else begin
       v.pos <- visit - 1;
       k First_visit;
       v.pos <- visit
     end
let fv_gen_visit_neg env visit fv k =
  match fv_gen_visit_counts env fv with
  | None -> ()
  | Some v ->
     assert (v.neg <= visit);
     if v.neg = visit then () (* visited already *)
     else if v.neg = visit - 1 then k Recursive_visit
     else begin
       v.neg <- visit - 1;
       k First_visit;
       v.neg <- visit
     end


(*
 * Opening/closing of binders
 *)

(* Assert that a typ contains no Vbound *)
let assert_locally_closed_var ix = function
  | Vrigid _ | Vflex _ -> ()
  | Vbound {index; _} -> assert (index < ix)

let rec assert_locally_closed :
  'a 'b . int -> ('a, 'b) typ -> unit =
  fun ix ty -> match ty with
  | Tsimple _ -> ()
  | Tcons (_,c) -> ignore (map_head (assert_locally_closed ix) (assert_locally_closed ix) c)
  | Tvar (_, v) -> assert_locally_closed_var ix v
  | Tvjoin (t, _, v) -> assert_locally_closed ix t; assert_locally_closed_var ix v
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     vars |> IArray.iter (fun (_, b) -> assert_locally_closed ix b);
     assert_locally_closed ix body

let map_head_cons pol f fields =
  map_fields (fun _fn x -> f pol x) fields

let tvjoin_opt t l v =
  match t with
  | None -> Tvar (l, v)
  | Some t -> Tvjoin (t, l, v)

let open_typ_var f rest loc ix = function
  | Vbound {index; var} when index >= ix ->
     assert (index = ix);
     Option.iter (assert_locally_closed ix) rest;
     let res = f rest loc var in
     assert_locally_closed ix res;
     res
  | v -> tvjoin_opt rest loc v

let rec open_typ :
  'neg 'pos . 
    neg:(('pos, 'neg) typ option -> Location.set -> int -> ('pos, 'neg) typ) ->
    pos:(('neg, 'pos) typ option -> Location.set -> int -> ('neg, 'pos) typ) ->
    int -> ('neg, 'pos) typ -> ('neg, 'pos) typ =
  fun ~neg ~pos ix t -> match t with
  | Tsimple _ as s -> s
  | Tcons (l,c) -> Tcons (l, map_head (open_typ ~neg:pos ~pos:neg ix) (open_typ ~neg ~pos ix) c)
  | Tvar (l,v) -> open_typ_var pos None l ix v
  | Tvjoin (t, l, v) -> open_typ_var pos (Some (open_typ ~neg ~pos ix t)) l ix v
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, open_typ ~neg:pos ~pos:neg ix b) vars;
            body = open_typ ~neg ~pos ix body}

let open_typ_rigid vars t =
  let mkv rest loc i = tvjoin_opt rest loc (Vrigid (IArray.get vars i)) in
  open_typ ~neg:mkv ~pos:mkv 0 t
let open_typ_flex vars t =
  let mkv rest loc i = tvjoin_opt rest loc (Vflex (IArray.get vars i)) in
  open_typ ~neg:mkv ~pos:mkv 0 t


let close_typ_var lvl f ~ispos ~isjoin index = function
  | Vrigid {level; _} as v when Env_level.equal lvl level ->
     Vbound {index; var = f v ~ispos ~isjoin}
  | Vflex fv as v when Env_level.equal lvl fv.level ->
     Vbound {index; var = f v ~ispos ~isjoin}
  | v -> v

(* Can only be used on typs without Tsimple nodes.
   (This limits it to use during parsing, which does not generate Tsimple) *)
let rec close_typ :
  'a 'b . env_level -> (typ_var -> ispos:bool -> isjoin:bool -> int) -> ispos:bool -> int -> (zero, zero) typ -> ('a, 'b) typ
  = fun lvl var ~ispos ix ty -> match ty with
  | Tsimple z -> never z
  | Tcons (l, c) -> Tcons (l, map_head (close_typ lvl var ~ispos:(not ispos) ix) (close_typ lvl var ~ispos ix) c)
  | Tvar (l, v) -> Tvar (l, close_typ_var lvl var ~ispos ~isjoin:false ix v)
  | Tvjoin (t, l, v) -> 
     Tvjoin(close_typ lvl var ~ispos ix t,
            l, close_typ_var lvl var ~ispos ~isjoin:true ix v)
  | Tpoly {vars; body} ->
     let ix = ix + 1 in
     Tpoly {vars = IArray.map (fun (n, b) -> n, close_typ lvl var ~ispos:(not ispos) ix b) vars;
            body = close_typ lvl var ~ispos ix body}

let close_typ_rigid ~ispos level ty =
  let close_var v ~ispos ~isjoin =
    (* FIXME report this better *)
    if isjoin && not ispos then failwith "contravariant join";
    match v with
    | Vrigid v when Env_level.equal v.level level -> v.var
    | _ -> intfail "close_typ_rigid: not a rigid variable" in
  close_typ level close_var ~ispos 0 ty


let next_flexvar_id = ref 0
let fresh_flexvar level : flexvar =
  let id = !next_flexvar_id in
  incr next_flexvar_id;
  { level; upper = []; lower = bottom; id; gen = Not_generalising }


(*
FIXME: this is needed for parsing. Even flexible variables can be looked up!

let rec env_lookup_type_var env name : (styp * styp) option =
  match env with
  | Env_cons { level; entry = (Erigid { names; _ } | Eflexible { names; _ }); _ }
       when SymMap.mem name names ->
     (* FIXME shifting? *)
     let i = SymMap.find name names in
     Some (styp_var Neg level i,
           styp_var Pos level i)
  | Env_cons { rest; _ } -> env_lookup_type_var rest name
  | Env_nil -> None
*)

 
let rec env_lookup_type_var env name : rigvar option =
  match env with
  | Env_vals vs -> env_lookup_type_var vs.rest name
  | Env_types ts ->
     begin match SymMap.find name ts.rig_names with
     | var -> Some {level = ts.level; var}
     | exception Not_found -> env_lookup_type_var ts.rest name
     end
  | Env_nil -> None

let lookup_named_type = function
  | "any" -> Some Top
  | "nothing" -> Some Bot
  | "bool" -> Some Bool
  | "int" -> Some Int
  | "string" -> Some String
  | _ -> None

let flexvar_name fv =
  let names = [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "κ"; "ν"; "ξ"; "π"; "ρ" |] in
  let id = fv.id in
  if id < Array.length names then names.(id)
  else Printf.sprintf "_%d" id


(*
 * Well-formedness checks.
 *)

let rec wf_flexvar ~seen env lvl (fv : flexvar) =
  if Hashtbl.mem seen fv.id then () else begin
  Hashtbl.add seen fv.id ();
  if not (Env_level.extends fv.level (env_level env)) then
    intfail "wf_flexvar: %s at %d not inside env %d" (flexvar_name fv) (Env_level.to_int fv.level) (Env_level.to_int (env_level env));
  assert (Env_level.extends fv.level (env_level env));
  assert (Env_level.extends fv.level lvl);
  if not (Env_level.equal fv.level Env_level.initial) then
    ignore (env_rigid_vars env fv.level);
  (* FIXME rectypes *)
  List.iter (fun fv' -> assert (fv != fv')) fv.lower.flexvars;
  wf_flex_lower_bound ~seen env fv.level fv.lower;
  (* Rigvar sets must be distinct *)
  let rvsets = List.filter_map (function UBvar _ -> None | UBcons c -> Some c.rigvars) fv.upper in
  assert (List.length rvsets = List.length (List.sort_uniq Rvset.compare rvsets));
  fv.upper |> List.iter (function
  | UBvar v ->
     wf_flexvar ~seen env fv.level v
  | UBcons {cons;rigvars;cons_locs=_} ->
     (* Each rigvar set must contain all of the rigvars in the lower bound *)
     let rvlow = Rvset.to_list fv.lower.ctor.rigvars in
     (* Well-formedness of bounds *)
     rvlow |> List.iter (fun rv -> assert (Rvset.contains rigvars rv));
     map_head (wf_flex_lower_bound ~seen env fv.level) (wf_flexvar ~seen env fv.level) cons |> ignore)
  end

and wf_rigvar env lvl (rv : rigvar) =
  assert (Env_level.extends rv.level lvl);
  let rvs = env_rigid_vars env rv.level in
  assert (0 <= rv.var && rv.var < IArray.length rvs)

and wf_flex_lower_bound ~seen env lvl ({ctor={cons;rigvars;cons_locs=_}; flexvars} : flex_lower_bound) =
  (* FIXME check for duplicate vars? (Not really a problem, but annoying) *)
  List.iter (wf_flexvar ~seen env lvl) flexvars;
  List.iter (wf_rigvar env lvl) (Rvset.to_list rigvars);
  map_head (wf_flexvar ~seen env lvl) (wf_flex_lower_bound ~seen env lvl) cons |> ignore



let wf_var ~seen env ext = function
  | Vflex fv -> wf_flexvar ~seen env fv.level fv
  | Vrigid rv -> wf_rigvar env rv.level rv
  | Vbound {index; var} ->
     assert (0 <= index && index < List.length ext);
     assert (0 <= var && var < snd (List.nth ext index))

let rec wf_typ : 'pos 'neg .
  seen:_ ->
  neg:('neg -> unit) ->
  pos:('pos -> unit) ->
  ispos:bool -> env -> (bool * int) list -> ('neg, 'pos) typ -> unit =
  fun ~seen ~neg ~pos ~ispos env ext ty ->
  match ty with
  | Tsimple s -> pos s
  | Tcons (_, c) ->
     map_head (wf_typ ~seen ~neg:pos ~pos:neg ~ispos:(not ispos) env ext) (wf_typ ~seen ~neg ~pos ~ispos env ext) c |> ignore
  | Tvar (_, v) -> wf_var ~seen env ext v
  | Tvjoin (t, _, v) ->
     wf_var ~seen env ext v;
     begin match v with
     | Vbound v ->
        assert (fst (List.nth ext v.index) = ispos); (* covariant *)
        (* Tvjoin restriction: in T | b, where b is a bound var, T must not mention deeper bindings *)
        let ext = List.mapi (fun ix (pol, len) -> if ix < v.index then (pol, 0) else (pol, len)) ext in
        wf_typ ~seen ~neg ~pos ~ispos env ext t
     | Vflex _ ->
        assert ispos; (* positive *)
        wf_typ ~seen ~neg ~pos ~ispos env [] t
     | Vrigid _ ->
        wf_typ ~seen ~neg ~pos ~ispos env [] t
     end
  | Tpoly {vars; body} ->
     let n_unique_vars = IArray.to_list vars |> List.map fst |> List.sort_uniq String.compare |> List.length in
     assert (n_unique_vars = IArray.length vars);
     let ext = (ispos, IArray.length vars) :: ext in
     IArray.iter (fun (_, c) ->
       (* FIXME: constraints on c. Can it be e.g. Tsimple?
          Not Vflex, at least. Prob not same binder either. *)
       wf_typ ~seen ~neg:pos ~pos:neg ~ispos:(not ispos) env ext c) vars;
     wf_typ ~seen ~neg ~pos ~ispos env ext body



(*
 * Unparsing: converting a typ back to a Exp.tyexp
 *)

let loc : Location.t =
 { source = "<none>";
   loc_start = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0};
   loc_end = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0} }

let mktyexp t = (Some t, loc)

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, loc)

let unparse_cons ~neg ~pos ty =
  let ty = match ty with
    | Top -> named_type "any"
    | Bot -> named_type "nothing"
    | Bool -> named_type "bool"
    | Int -> named_type "int"
    | String -> named_type "string"
    | Record fs ->
       Trecord (Tuple_fields.map_fields (fun _ t -> pos t) fs)
    | Func (args, ret) ->
       Tfunc (Tuple_fields.map_fields (fun _ t -> neg t) args,
              pos ret) in
  mktyexp ty

let unparse_bound_var ~ext index var =
  let name =
    if index < List.length ext then
      IArray.get (List.nth ext index) var
    else
      match index - List.length ext with
      | 0 -> Printf.sprintf "$%d" var
      | n -> Printf.sprintf "$%d.%d" n var in
  mktyexp (named_type name)


let unparse_rigid_var {level;var} =
  mktyexp (named_type (Printf.sprintf "%d.%d" (Env_level.to_int level) var))

let unparse_flexvar ~flexvar fv =
  flexvar fv;
  let name = flexvar_name fv in
(*  let name = Printf.sprintf "%s@%d" name (Env_level.to_int fv.level) in*)
  mktyexp (named_type name)

let unparse_var ~flexvar ~ext = function
  | Vbound {index; var} -> unparse_bound_var ~ext index var
  | Vflex fv -> unparse_flexvar ~flexvar fv
  | Vrigid rv -> unparse_rigid_var rv

let unparse_join ty (rigvars : Rvset.t) =
  List.fold_left (fun c r -> mktyexp (Exp.Tjoin (c, unparse_rigid_var r))) ty (Rvset.to_list rigvars)

let rec unparse_gen_typ :
  'neg 'pos . flexvar:_ -> ext:_ -> neg:('neg -> Exp.tyexp) -> pos:('pos -> Exp.tyexp) ->
             ('neg,'pos) typ -> Exp.tyexp =
  fun ~flexvar ~ext ~neg ~pos ty -> match ty with
  | Tsimple t -> pos t
  | Tcons (_, c) -> unparse_cons ~neg:(unparse_gen_typ ~flexvar ~ext ~neg:pos ~pos:neg) ~pos:(unparse_gen_typ ~flexvar ~ext ~neg ~pos) c
  | Tvar (_, var)
  | Tvjoin (Tcons (_, Bot), _, var) ->
     unparse_var ~flexvar ~ext var
  | Tvjoin (rest, _, var) ->
     mktyexp (Exp.Tjoin (unparse_gen_typ ~flexvar ~ext ~neg ~pos rest, unparse_var ~flexvar ~ext var))
  | Tpoly { vars; body } ->
     let ext, bounds = unparse_bounds ~flexvar ~ext ~neg ~pos vars in
     mktyexp (Exp.Tforall(bounds, unparse_gen_typ ~flexvar ~ext ~neg ~pos body))

and unparse_bounds :
  'neg 'pos . flexvar:_ -> ext:_ -> neg:('neg -> Exp.tyexp) -> pos:('pos -> Exp.tyexp) ->
             (string * ('pos,'neg) typ) iarray -> _ * Exp.typolybounds =
  fun ~flexvar ~ext ~neg ~pos vars ->
  (* FIXME: this sort of freshening or shifts? *)
  (* FIXME: if freshening, use levels somehow to determine when not needed *)
  let taken name =
    lookup_named_type name <> None || List.exists (fun names -> IArray.exists (String.equal name) names) ext in
  let rec freshen name i =
    let p = Printf.sprintf "%s_%d" name i in
    if not (taken p) then p else freshen name (i + 1) in
  let freshen name =
    if not (taken name) then name else freshen name 2 in
  let vars = IArray.map (fun (s, b) -> freshen s, b) vars in
  let ext = IArray.map fst vars :: ext in
  ext, IArray.map (fun (s, bound) ->
       let s = (s, loc) in
       match bound with
       | Tcons (_, Top) ->
          s, None
       | t ->
          s, Some (unparse_gen_typ ~flexvar ~ext ~pos:neg ~neg:pos t)) vars |> IArray.to_list

let rec unparse_flex_lower_bound ~flexvar { ctor; flexvars } =
  let t =
    match ctor with
    | { cons = Bot; rigvars; cons_locs=_ } when Rvset.(equal rigvars empty) -> None
    | { cons; rigvars; cons_locs=_ } ->
       let cons = unparse_cons ~neg:(unparse_flexvar ~flexvar) ~pos:(unparse_flex_lower_bound ~flexvar) cons in
       Some (unparse_join cons rigvars) in
  let tjoin a b =
    match a with
    | None -> Some b
    | Some a -> Some (mktyexp (Exp.Tjoin (a, b))) in
  match
    List.fold_left (fun t fv -> tjoin t (unparse_flexvar ~flexvar fv)) t flexvars
  with
  | Some t -> t
  | None -> unparse_cons ~neg:never ~pos:never Bot

let unparse_styp_neg ~flexvar = function
  | UBvar v -> unparse_flexvar ~flexvar v
  | UBcons {cons;rigvars;cons_locs=_} ->
     let cons = unparse_cons ~neg:(unparse_flex_lower_bound ~flexvar) ~pos:(unparse_flexvar ~flexvar) cons in
     unparse_join cons rigvars

let unparse_ptyp ~flexvar ?(ext=[]) (t : ptyp) =
  unparse_gen_typ ~flexvar ~ext ~neg:(unparse_flexvar ~flexvar) ~pos:(unparse_flex_lower_bound ~flexvar) t
let unparse_ntyp ~flexvar ?(ext=[]) (t : ntyp) =
  unparse_gen_typ ~flexvar ~ext ~neg:(unparse_flex_lower_bound ~flexvar) ~pos:(unparse_flexvar ~flexvar) t



(* For debugging *)
let pp_doc ppf doc =
  let buf = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. 10000 buf (PPrint.group doc);
  Format.fprintf ppf "%s" (Buffer.to_bytes buf |> Bytes.to_string)

let pp_tyexp ppf ty =
  let ty = Exp.map_tyexp Exp.normalise ty in
  pp_doc ppf (Print.tyexp ty)

let pp_exp ppf e =
  pp_doc ppf (Print.exp e)

let pp_cons_pos ppf t =
  let cons = unparse_cons ~neg:(unparse_flexvar ~flexvar:ignore) ~pos:(unparse_flex_lower_bound ~flexvar:ignore) t.cons in
  let doc = unparse_join cons t.rigvars in
  pp_tyexp ppf doc

let pp_cons_neg ppf t =
  let cons = unparse_cons ~neg:(unparse_flex_lower_bound ~flexvar:ignore) ~pos:(unparse_flexvar ~flexvar:ignore)  t.cons in
  let doc = unparse_join cons t.rigvars in
  pp_tyexp ppf doc

let pp_flexlb ppf t =
  let doc = unparse_flex_lower_bound ~flexvar:ignore t in
  pp_tyexp ppf doc

let pp_styp_neg ppf t =
  let tys = List.map (unparse_styp_neg ~flexvar:ignore) t in
  let docs = List.map (fun t -> Print.tyexp (Exp.map_tyexp Exp.normalise t)) tys in
  pp_doc ppf (PPrint.(separate (comma ^^ space) docs))

let pp_flexvar ppf v =
  pp_tyexp ppf (unparse_flexvar ~flexvar:ignore v)

let pp_ntyp ppf t =
  pp_tyexp ppf (unparse_ntyp ~flexvar:ignore t)

let pp_ptyp ppf t =
  pp_tyexp ppf (unparse_ptyp ~flexvar:ignore t)

let dump_ptyp ppf t =
  let fvs = Hashtbl.create 20 in
  let fv_list = ref [] in
  let _name_ix = ref 0 in
  let rec flexvar fv =
    match Hashtbl.find fvs fv.id with
    | _ -> ()
    | exception Not_found ->
       let fv_name = flexvar_name fv in
       Hashtbl.add fvs fv.id (fv_name, None);
       fv_list := fv.id :: !fv_list;
       let l =
         if equal_flex_lower_bound fv.lower bottom then None
         else Some (unparse_flex_lower_bound ~flexvar fv.lower) in
       let u = List.map (unparse_styp_neg ~flexvar) fv.upper in
       Hashtbl.replace fvs fv.id (fv_name, Some (l, u));
       ()
  and unparse t =
    unparse_ptyp ~flexvar t
  in
  let t = unparse t in
  let fvs = !fv_list |> List.rev |> List.map (fun i -> let (n, t) = (Hashtbl.find fvs i) in n, Option.get t) in
  Format.fprintf ppf "%a\n" pp_tyexp t;
  fvs |> List.iter (function
    | n, (l, us) ->
       begin match l with
       | Some l -> 
          Format.fprintf ppf " %a <= %s" pp_tyexp l n
       | None ->
          Format.fprintf ppf "      %s" n
       end;
       us |> List.iteri (fun i u ->
         Format.fprintf ppf "%s %a" (if i = 0 then " <=" else ";") pp_tyexp u);
       Format.fprintf ppf "\n")

let pp_changes ppf changes =
  Format.fprintf ppf "[";
  List.rev changes |> List.iteri (fun i ch ->
    let sp = if i = 0 then "" else " " in
    let pv fv ty =
      Format.fprintf ppf "%s%s%s" sp (flexvar_name fv) ty in
    match ch with
    | Change_expanded_mark -> Format.fprintf ppf "%s!" sp
    | Change_upper(v,_) -> pv v "-"
    | Change_lower(v,_) -> pv v "+"
    | Change_level(v,_) -> pv v "@");
  Format.fprintf ppf "]"



let wf_ptyp env (t : ptyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~seen ~neg:(wf_flexvar ~seen env (env_level env)) ~pos:(wf_flex_lower_bound ~seen env (env_level env)) ~ispos:true env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ptyp t

let wf_ntyp env (t : ntyp) =
  try
    let seen = Hashtbl.create 10 in
    wf_typ ~seen ~neg:(wf_flex_lower_bound ~seen env (env_level env)) ~pos:(wf_flexvar ~seen env (env_level env)) ~ispos:false env [] t
  with
  | Assert_failure (file, line, _char) when file = __FILE__ ->
     intfail "Ill-formed type (%s:%d): %a" file line pp_ntyp t
