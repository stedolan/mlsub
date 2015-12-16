type polarity = Pos | Neg

let polneg = function Pos -> Neg | Neg -> Pos
let polmul = function Pos -> (fun p -> p) | Neg -> polneg

let pol_flip f pol x y = match pol with Pos -> f x y | Neg -> f y x

(* FIXME *)
module SMap = Map.Make (struct type t = int let compare = compare end)

type 'a printer = Format.formatter -> 'a -> unit
let print_to_string (pr : 'a printer) (x : 'a) : string =
  let buf = Buffer.create 100 in
  let ppf = Format.formatter_of_buffer buf in
  Format.fprintf ppf "%a%!" pr x;
  Buffer.contents buf
  

module Reason = struct
  type t = 
    | Conflict of Location.set * string * Location.set * string
  let print ppf (Conflict (la, a, lb, b)) = 
    Location.LocSet.iter (Location.print ppf) la;
    Location.LocSet.iter (Location.print ppf) lb;
    Format.fprintf ppf "%s - %s\n%!" a b
  let excuse = Conflict (Location.empty, "?", Location.empty, "?")
end
  


module type FEATURE = sig
    type 'a t
    (* join Pos is least-upper-bound, join Neg is greatest-lower-bound. *)
    val join : polarity -> (polarity -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    (* lte Pos f a b is a <= b, lte Neg f a b is a >= b. f works the same way *)
    val lte : polarity -> (polarity -> 'a -> 'b -> Reason.t list) -> 'a t -> 'b t -> Reason.t list

    val pmap : (polarity -> 'a -> 'b) -> polarity -> 'a t -> 'b t
    val pfold : (polarity -> 'a -> 'r -> 'r) -> polarity -> 'a t -> 'r -> 'r

    val print : (polarity -> 'a printer) -> polarity -> 'a t printer
    val list_fields : 'a t -> (string * 'a) list
    val name : string

    val locations : 'a t -> Location.set
    val change_locations : Location.set -> 'a t -> 'a t
  end

module Func = struct
  type 'a t = Func of Location.set * 'a * 'a
  let join p f (Func (l,d,r)) (Func (l',d',r')) = Func (Location.join l l', f (polneg p) d d', f p r r')
  let lte pol f (Func (l, d, r)) (Func (l', d', r')) = f (polneg pol) d d' @ f pol r r'

  let pmap f pol (Func (l, d, r)) = Func (l, f (polneg pol) d, f pol r)
  let pfold f pol (Func (l, d, r)) x = f (polneg pol) d (f pol r x)

  let print pr pol ppf (Func (_, d, r)) =
    Format.fprintf ppf "%a -> %a" (pr (polneg pol)) d (pr pol) r
  let list_fields (Func (_, d, r)) = ["d", d; "r", r]
  let name = "function"
  let locations (Func (l, _, _)) = l
  let change_locations l' (Func (l, d, r)) = Func (l', d, r)
end

module ListT = struct
  type 'a t = Location.set * 'a
  let join p f (la, a) (lb, b) = (Location.join la lb, f p a b)
  let lte pol f (_, a) (_, b) = f pol a b
  let pmap f pol (l, a) = (l, f pol a)
  let pfold f pol (l, a) r = f pol a r
  let print pr pol ppf (_, a) =
    Format.fprintf ppf "%a list" (pr pol) a
  let list_fields (_, x) = ["e", x]
  let name = "list"
  let locations (l, _) = l
  let change_locations l' (l, a) = l', a
end

module Object = struct
  type 'a t = (Location.set * 'a) SMap.t
  let join p f x y =
    let m = match p with
      | Pos -> fun k x y -> (match x, y with (* lub takes intersection of fields *)
                             | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Pos x y)
                             | _, _ -> None)
      | Neg -> fun k x y -> (match x, y with (* glb takes union of fields *)
                             | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Neg x y)
                             | Some a, None
                             | None, Some a -> Some a
                             | None, None -> None) in
    SMap.merge m x y
  let locations (o : 'a t) = 
    SMap.fold (fun _ (l, _) locs -> Location.join l locs) o Location.empty
  let change_locations l' o =
    SMap.map (fun (l, a) -> (l', a)) o

  let lte pol f x y : Reason.t list =
    match pol with
    | Pos -> 
       SMap.fold (fun k (yl, yk) r -> 
         if SMap.mem k x then
           let (xl, xk) = SMap.find k x in
           f pol xk yk @ r
         else [Reason.Conflict (locations x, "{}", yl, Symbol.to_string k)] @ r) y []
    | Neg ->
       SMap.fold (fun k (xl, xk) r ->
         if SMap.mem k y then
           let (yl, yk) = SMap.find k y in
           f pol xk yk @ r
         else [Reason.Conflict (xl, Symbol.to_string k, locations y, "{}")] @ r) x []

  let pmap f pol o = SMap.map (fun (l, x) -> (l, f pol x)) o
  let pfold f pol o r =
    SMap.fold (fun k (l, x) r -> f pol x r) o r

  let list_fields o = List.map (fun (k, (_, v)) -> (Symbol.to_string k, v)) (SMap.bindings o)

  let print pr pol ppf o =
    let rec pfield ppf = function
      | [] -> ()
      | [f, x] ->
         Format.fprintf ppf "%s :@ %a" f (pr pol) x
      | (f, x) :: xs ->
         Format.fprintf ppf "%s :@ %a,@ %a" f (pr pol) x pfield xs in
    Format.fprintf ppf "{%a}" pfield (list_fields o)

  let name = "object"
end

module type TYPES = sig
    type 'a t
    val join : polarity -> (polarity -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    val join_ident : 'a t

    val check_join_ident : 'a t -> (string * Location.set) list

    val lte_pn : ('a -> 'a -> Reason.t list) -> 'a t -> 'a t -> Reason.t list
    val lte_np : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val subs : polarity -> (polarity -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

    val pmap : (polarity -> 'a -> 'b) -> polarity -> 'a t -> 'b t
    val pfold : (polarity -> 'a -> 'r -> 'r) -> polarity -> 'a t -> 'r -> 'r

    val print_first : (polarity -> 'a printer) -> polarity -> 'a t printer
    val print_rest : (polarity -> 'a printer) -> polarity -> 'a t printer
    val list_fields : 'a t -> (string * 'a) list

    val change_locations : Location.set -> 'a t -> 'a t
  end

module Base = struct
  type 'a t = Location.set SMap.t (* FIXME: real sets of symbols would be nice *)
  let join p _ x y =
    SMap.merge (fun k x y -> match x, y with
      Some l, Some l' -> Some (Location.join l l')
    | (Some _ as l), None
    | None, (Some _ as l) -> l
    | None, None -> None) x y

  let join_ident = SMap.empty

  let check_join_ident t = List.map (fun (k, l) -> Symbol.to_string k, l) (SMap.bindings t)

  let lte_pn f x y : Reason.t list =
    (* x = y = singleton || x = empty || y = empty *)
    SMap.fold (fun k loc rs -> 
      SMap.fold (fun k' loc' rs -> 
        (if k = k' then [] else [Reason.Conflict (loc, Symbol.to_string k, loc', Symbol.to_string k')]) @ rs) y rs) x []

  let lte_np f x y =
    (* nonempty intersection *)
    SMap.exists (fun k _ -> SMap.mem k x) y

  let subs p f x y =
    let subset a b = SMap.for_all (fun k _ -> SMap.mem k b) a in
    pol_flip subset p x y

  let pmap f pol x = x
  let pfold f pol x r = r

  let print_rest  pr pol ppf x =
    SMap.iter (fun k _ -> Format.fprintf ppf "@ %s@ %s" (match pol with Pos -> "|" | Neg -> "&") (Symbol.to_string k)) x

  let print_first pr pol ppf x =
    if SMap.is_empty x then
      Format.fprintf ppf "%s" (match pol with Pos -> "Bot" | Neg -> "Top")
    else
      let (k, _) = SMap.min_binding x in
      Format.fprintf ppf "%s%a" (Symbol.to_string k) (print_rest pr pol) (SMap.remove k x)

  let list_fields _ = []

  let change_locations l' t = SMap.map (fun _ -> l') t
end

module Cons (A : FEATURE) (Tail : TYPES) = struct
  module Tail = Tail

  type 'a t =
    | Present of 'a A.t * 'a Tail.t
    | Absent of 'a Tail.t

  let join p f x y =
    match x, y with
    | Present (xa, xt), Present (ya, yt) ->
       Present (A.join p f xa ya, Tail.join p f xt yt)
    | Present (a, xt), Absent yt
    | Absent xt, Present (a, yt) ->
       Present (a, Tail.join p f xt yt)
    | Absent xt, Absent yt ->
       Absent (Tail.join p f xt yt)

  let join_ident =
    Absent Tail.join_ident

  let check_join_ident = function
    | Present (a, t) -> (A.name, A.locations a) :: Tail.check_join_ident t
    | Absent t -> Tail.check_join_ident t

  let lte_pn f x y =
    (* lub X <= glb Y *)
    (* i.e. forall i,j, Xi <= Yj *)
    let check_x yl yn xt =
      Tail.check_join_ident xt |>
          List.map (fun (xn, xl) -> Reason.Conflict (xl, xn, yl, xn)) in
    let check_y xl xn yt =
      Tail.check_join_ident yt |>
          List.map (fun (yn, yl) -> Reason.Conflict (xl, xn, yl, yn)) in
    match x, y with
    | Present (xa, xt), Present (ya, yt) ->
       A.lte Pos (pol_flip f) xa ya @
         check_x (A.locations ya) A.name xt @
         check_y (A.locations xa) A.name yt
    | Present (xa, xt), Absent yt ->
       check_y (A.locations xa) A.name yt
    | Absent xt, Present (ya, yt) ->
       check_x (A.locations ya) A.name xt
    | Absent xt, Absent yt ->
       Tail.lte_pn f xt yt

  let lte_np f x y =
    (* glb X <= lub Y *)
    (* i.e. exists i,j, Xi <= Yj *)
    match x, y with
    | Present (xa, xt), Present (ya, yt) ->
       A.lte Pos (fun p x y -> if pol_flip f p x y then [] else [Reason.excuse]) xa ya = [] || Tail.lte_np f xt yt
    | Present (_, xt), Absent yt
    | Absent xt, Present (_, yt)
    | Absent xt, Absent yt ->
      Tail.lte_np f xt yt

  let subs pol f x y =
    match x, y with
    | Present (xa, xt), Present (ya, yt) ->
       A.lte pol (fun p x y -> if f p x y then [] else [Reason.excuse]) xa ya = [] && Tail.subs pol f xt yt
    | Present (xa, xt), Absent yt ->
       false
    | Absent xt, (Present (_, yt) | Absent yt) ->
       Tail.subs pol f xt yt


  let pmap f pol = function
    | Absent t -> Absent (Tail.pmap f pol t)
    | Present (a, t) -> Present (A.pmap f pol a, Tail.pmap f pol t)

  let pfold f pol a r = match a with
    | Absent t -> Tail.pfold f pol t r
    | Present (a, t) -> A.pfold f pol a (Tail.pfold f pol t r)
       
  let lift x = Present (x, Tail.join_ident)

  let print_rest pr pol ppf = function
    | Absent t -> Tail.print_rest pr pol ppf t
    | Present (a, t) ->
       let sep = match pol with Pos -> "|" | Neg -> "&" in
       Format.fprintf ppf "@ %s@ %a%a" sep (A.print pr pol) a (Tail.print_rest pr pol) t

  let print_first pr pol ppf = function
    | Absent t -> Tail.print_first pr pol ppf t
    | Present (a, t) ->
       Format.fprintf ppf "%a%a" (A.print pr pol) a (Tail.print_rest pr pol) t

  let list_fields = function
    | Present (a, t) -> A.list_fields a @ Tail.list_fields t
    | Absent t -> Tail.list_fields t

  let change_locations l' = function
    | Present (a, t) -> Present (A.change_locations l' a, Tail.change_locations l' t)
    | Absent t -> Absent (Tail.change_locations l' t)
end


module Ty2 = Cons (Object) (Base)
module Ty1 = Cons (Func) (Ty2)
module Ty0 = Cons (ListT) (Ty1)
module TypeLat = struct
    include Ty0
    let iter f p x = pfold (fun pol x r -> f pol x) p x ()
end

let cons_list e : 'a TypeLat.t =
  Ty0.lift e
let cons_func f : 'a TypeLat.t = 
  Ty0.Absent (Ty1.lift f)
let cons_object o : 'a TypeLat.t =
  Ty0.Absent (Ty1.Absent (Ty2.lift o))
let cons_base x loc : 'a TypeLat.t =
  Ty0.Absent (Ty1.Absent (Ty2.Absent (SMap.singleton x loc)))


let cons_name pol = print_to_string (TypeLat.print_first (fun pol ppf x -> ()) pol)


type var = string

type 'a typeterm = 
| TVar of 'a
| TCons of ('a typeterm) TypeLat.t
| TAdd of 'a typeterm * 'a typeterm
| TRec of 'a * 'a typeterm


let ty_add t t' loc = TAdd (t loc, t' loc)
let ty_var v loc = TVar v
let ty_list e loc = TCons (cons_list (Location.one loc, e loc))
let ty_fun d r loc = TCons (cons_func (Func.Func (Location.one loc, d loc, r loc)))
let ty_zero loc = TCons (TypeLat.join_ident)
let ty_obj o loc = TCons (cons_object (SMap.map (fun x -> (Location.one loc, x loc)) o))
let ty_base s loc = TCons (cons_base s (Location.one loc))
                       
let string_of_var v = v

open Format

let printp paren ppf fmt =
  let openbox ppf = if paren then fprintf ppf "@[(" else fprintf ppf "@[" in
  let closebox ppf = if paren then fprintf ppf "@])" else fprintf ppf "@]" in
  openbox ppf;
  kfprintf closebox ppf fmt


let rec gen_print_typeterm vstr pol ppf = function
  | TVar v -> fprintf ppf "%s" (vstr v)
  | TCons cons ->
     fprintf ppf "@[(%a)@]" (TypeLat.print_first (gen_print_typeterm vstr) pol) cons
  | TAdd (t1, t2) -> 
    let op = match pol with Pos -> "|" | Neg -> "&" in
    fprintf ppf "@[(%a %s@ %a)@]" (gen_print_typeterm vstr pol) t1 op (gen_print_typeterm vstr pol) t2
  | TRec (v, t) ->
    fprintf ppf "rec %s = %a" (vstr v) (gen_print_typeterm vstr pol) t

let print_typeterm = gen_print_typeterm string_of_var



type state_id = int


module rec State : sig
  type state = 
    { id : state_id;
      pol : polarity;
      mutable cons : StateSet.t TypeLat.t;
      mutable flow : StateSet.t; }
end = struct
  type state =
    { id : state_id;
      pol : polarity;
      mutable cons : StateSet.t TypeLat.t;
      mutable flow : StateSet.t }
end
and StateSet : Intmap.S with type elt = State.state = 
  Intmap.Fake (struct type t = State.state let get_id = State.(fun s -> s.id) end)

open State
type state = State.state

module StateHash = struct type t = state let equal x y = x == y let hash x = x.id end
module StateTbl = Hashtbl.Make (StateHash)


module VarOrd = struct type t = var let compare = compare end
module VarMap = Map.Make (VarOrd)

let state_cons_join p x y =
  let merge p x y = 
    StateSet.iter x (fun s -> assert (s.pol = p));
    StateSet.iter y (fun s -> assert (s.pol = p));
    StateSet.union x y in
  TypeLat.join p merge x y

let merge s s' =
  assert (s.pol = s'.pol);
  s.cons <- state_cons_join s.pol s.cons s'.cons;
  s.flow <- StateSet.union s.flow s'.flow;
  StateSet.iter s.flow (fun s' -> assert (s'.pol <> s.pol))


let fresh_id_counter = ref 0
let fresh_id () =
  let n = !fresh_id_counter in incr fresh_id_counter; n

(* FIXME: Does not detect negative recursion *)
let compile_terms (map : (polarity -> var typeterm -> state) -> 'a) : 'a =
  let states = ref [] in
  let mkstate pol cons = 
    let r = { id = fresh_id (); pol; cons; flow = StateSet.empty } in
    (states := r :: !states; r) in
  let state_vars = StateTbl.create 20 in
  let epsilon_trans = StateTbl.create 20 in
  let rec compile r p = function
    | TVar v -> (
      try VarMap.find v r
      with Not_found ->
        (let s = mkstate p TypeLat.join_ident in
         StateTbl.add state_vars s v; s))
    | TCons c -> mkstate p (TypeLat.pmap (fun p t -> StateSet.singleton (compile r p t)) p c) 
    | TAdd (t1, t2) ->
      let s1, s2 = compile r p t1, compile r p t2 in
      let s = mkstate p TypeLat.join_ident in
      StateTbl.add epsilon_trans s s1;
      StateTbl.add epsilon_trans s s2;
      s
    | TRec (v, t) ->
      let s = mkstate p TypeLat.join_ident in
      let s' = compile (VarMap.add v s r) p t in
      StateTbl.add epsilon_trans s s';
      s in
  let root = map (compile VarMap.empty) in

  (* FIXME: would it be cleaner to remove eps-trans after adding flow constraints? *)

  (* Remove epsilon transitions *)
  let rec epsilon_closure set s =
    if StateSet.mem set s then set
    else List.fold_left epsilon_closure (StateSet.add set s) (StateTbl.find_all epsilon_trans s) in
  let epsilon_merge s states =
    s.cons <- List.fold_left (state_cons_join s.pol) s.cons (List.map (fun s -> s.cons) states);
    List.iter (fun s' -> 
      List.iter 
        (fun v -> StateTbl.add state_vars s v)
        (StateTbl.find_all state_vars s')) states in
  List.iter (fun s -> epsilon_merge s (StateSet.to_list (epsilon_closure StateSet.empty s))) !states;


  (* Add flow constraints *)
  let collect_constraint s v (vn, vp) =
    let ins map st var = 
      VarMap.add var (StateSet.add (try VarMap.find var map with Not_found -> StateSet.empty) st) map in
    match s.pol with Pos -> (vn, ins vp s v) | Neg -> (ins vn s v, vp) in
  let var_state_neg, var_state_pos = 
    StateTbl.fold collect_constraint state_vars (VarMap.empty, VarMap.empty) in
  let add_constraints s v = 
    let map = (match s.pol with Pos -> var_state_neg | Neg -> var_state_pos) in
    let states = try VarMap.find v map with Not_found -> StateSet.empty in
    s.flow <- StateSet.union s.flow states in
  StateTbl.iter add_constraints state_vars; 

  root

let print_automaton diagram_name id ppf (map : (string -> state -> unit) -> unit) =
  let dumped = StateTbl.create 20 in
  let pstate ppf s = fprintf ppf "n%d" s.id in
  let rec dump s name =
    if StateTbl.mem dumped s then () else begin
      StateTbl.add dumped s s;
      let name = (match name with None -> "" | Some n -> n ^ ": ") ^ cons_name s.pol s.cons in
      fprintf ppf "%a [label=\"%s (%d)\"];\n" pstate s name (id s);
      List.iter (fun (f, ss') -> 
        StateSet.iter ss'
          (fun s' -> 
            fprintf ppf "%a -> %a [label=\"%s\"];\n" pstate s pstate s' f;
            dump s' None))
        (TypeLat.list_fields s.cons)
    end in
  fprintf ppf "digraph %s{\n" diagram_name;
  (* dump structural constraints *)
  map (fun n s -> dump s (Some n); ());
  (* dump dataflow constraints *)
  StateTbl.iter (fun s _ ->
    if s.pol = Neg then StateSet.iter s.flow (fun s' -> 
      try
        let s' = StateTbl.find dumped s' in
        fprintf ppf "%a -> %a [style=dashed, constraint=false]\n" pstate s pstate s'
      with Not_found -> ())) dumped;
  fprintf ppf "}\n"

let find_reachable (roots : state list) =
  let states = StateTbl.create 20 in
  let rec search s acc =
    if StateTbl.mem states s then acc else begin
      StateTbl.add states s ();
      s :: List.fold_right (fun (f, ss') acc -> StateSet.fold_left ss' acc
        (fun acc s' -> search s' acc)) (TypeLat.list_fields s.cons) acc
    end in
  List.fold_right search roots []

let garbage_collect (root : state) =
  let states = find_reachable [root] in
  let state_set = List.fold_left StateSet.add StateSet.empty states in
  List.iter (fun s -> s.flow <- StateSet.inter s.flow state_set) states
                
let make_table s f =
  let t = StateTbl.create 20 in
  StateSet.iter s (fun s -> StateTbl.add t s (f s)); 
  t

(* FIXME: deterministic? ID-dependent? *)
let decompile_automaton (root : state) : var typeterm =
  let state_list = find_reachable [root] in
  let states = List.fold_left StateSet.add StateSet.empty state_list in
  let state_flow = make_table states (fun s -> StateSet.inter s.flow states) in


  let check () =
    StateSet.iter states (fun s -> StateSet.iter (StateTbl.find state_flow s)
      (fun s' -> 
        assert (StateSet.mem (StateTbl.find state_flow s) s');
        assert (StateSet.mem (StateTbl.find state_flow s') s))) in

  let sane s = StateSet.iter s (fun x -> assert (StateSet.mem s x)) in

  let check2 () =
    StateSet.iter states (fun s -> sane s.flow; StateSet.iter s.flow
      (fun s' -> 
        assert (StateSet.mem s.flow s');
        assert (StateSet.mem s'.flow s))) in
  check2 ();
  (* Decompose flow constraints into variables.
     This is the biclique decomposition of a bipartite graph. Doing it optimally
     is NP-complete, we do it badly in polynomial time *)
  let principal_biclique s = 
    let ss' = StateTbl.find state_flow s in
    if StateSet.is_empty ss' then StateSet.(empty, empty) else begin
      let ss = StateSet.fold_left ss' states
        (fun m s' -> StateSet.inter (StateTbl.find state_flow s') m) in
      check ();
      (* fprintf err_formatter "found biclique %d %d\n%!" (StateSet.length ss) (StateSet.length ss'); *)
      (ss, ss') 
    end in
  let find_biclique () =
    List.fold_left
      (fun ((best_n, _, _) as best) s ->
        let (ss, ss') = principal_biclique s in
        let n = StateSet.(length ss + length ss') in
        if n > best_n then (n, ss, ss') else best)
      (0, StateSet.empty, StateSet.empty) state_list in
  let del_biclique ss ss' =
    let del ss ss' = 
      StateSet.iter ss (fun s -> 
        StateTbl.replace state_flow s
          (StateSet.diff (StateTbl.find state_flow s) ss')) in
    check (); del ss ss'; del ss' ss; check () in
  let rec find_biclique_decomposition () =
    let (n, ss, ss') = find_biclique () in
    (* fprintf err_formatter "best biclique: %d\n%!" n; *)
    if n = 0 then [] else begin
      del_biclique ss ss';
      (ss, ss') :: find_biclique_decomposition ()
    end in
  let biclique_decomposition = find_biclique_decomposition () in

  (* Each biclique in the decomposition corresponds to a variable *)
  let name_var id =
    if id < 26 then String.make 1 (Char.chr (Char.code 'a' + id)) else Printf.sprintf "v_%d" (id - 26) in
  let fresh_var = let var_id = ref (-1) in fun () -> incr var_id; name_var !var_id in
  let state_vars = StateTbl.create 20 in
  List.iter (fun (ss, ss') -> 
    let v = TVar (fresh_var ()) in
    let iter ss = StateSet.iter ss (fun s -> StateTbl.add state_vars s v) in
    iter ss; iter ss') biclique_decomposition;


  let rec term_add p = function
    | [] -> TCons TypeLat.join_ident
    | [t] -> t
    | (t :: ts) ->
      if t = TCons TypeLat.join_ident then term_add p ts else
        TAdd (t, term_add p ts) in

  let state_rec_var = StateTbl.create 20 in
  let rec decompile s =
    if StateTbl.mem state_rec_var s then
      match StateTbl.find state_rec_var s with
      | Some v -> TVar v
      | None -> let v = fresh_var () in (StateTbl.replace state_rec_var s (Some v); TVar v)
    else
      let vars = StateTbl.find_all state_vars s in
      StateTbl.add state_rec_var s None;
      let t = TypeLat.pmap (fun p' ss' -> term_add p' (List.map decompile (StateSet.to_list ss'))) s.pol s.cons in
      let tv = term_add s.pol (TCons t :: vars) in
      let visited = StateTbl.find state_rec_var s in
      StateTbl.remove state_rec_var s;
      match visited with
      | None -> tv
      | Some v -> TRec (v, tv) in
  decompile root
  


let contraction sp_orig sn_orig =
  assert (sp_orig.pol = Pos);
  assert (sn_orig.pol = Neg);
  let seen = Hashtbl.create 20 in
  let rec closure sp sn =
    if Hashtbl.mem seen (sp.id, sn.id) then []
    else begin
      Hashtbl.add seen (sp.id, sn.id) ();
      StateSet.iter sn.flow (fun s -> merge s sp);
      StateSet.iter sp.flow (fun s -> merge s sn);
      TypeLat.lte_pn closure_l sp.cons sn.cons
    end
  and closure_l ssp ssn =
    StateSet.fold_left ssp [] (fun rs sp ->
      rs @ StateSet.fold_left ssn rs (fun rs sn ->
        rs @ closure sp sn)) in
  closure sp_orig sn_orig




let states_follow p (s : StateSet.t) : StateSet.t TypeLat.t =
  StateSet.fold_left s TypeLat.join_ident (fun c s -> TypeLat.join p (fun p a b -> StateSet.union a b) c s.cons)


(* Deterministic automata *)


type dstate_id = int

module rec DState : sig
  type dstate = 
    { id : dstate_id;
      pol : polarity;
      mutable cons : dstate TypeLat.t;
      mutable flow : DStateSet.t; }
end = struct
  type dstate =
    { id : dstate_id;
      pol : polarity;
      mutable cons : dstate TypeLat.t;
      mutable flow : DStateSet.t }
end
and DStateSet : Intmap.S with type elt = DState.dstate = 
  Intmap.Fake (struct type t = DState.dstate let get_id = DState.(fun s -> s.id) end)

type dstate = DState.dstate
let fresh_dstate p =
  DState.{ id = fresh_id ();
           pol = p;
           cons = TypeLat.join_ident;
           flow = DStateSet.empty } 

module DStateHash = struct type t = dstate let equal x y = x == y let hash x = x.DState.id end
module DStateTbl = Hashtbl.Make (DStateHash)


(* Convert a DFA into an NFA *)
let clone f =
  let states = DStateTbl.create 20 in
  let rec copy_state loc s =
    if DStateTbl.mem states s then
      DStateTbl.find states s 
    else begin
      let s' = { id = fresh_id ();
                 pol = s.DState.pol;
                 cons = TypeLat.join_ident;
                 flow = StateSet.empty } in
      DStateTbl.add states s s';
      s'.cons <- TypeLat.pmap (fun pol d ->
        assert (pol = d.DState.pol);
        StateSet.singleton (copy_state loc d)) s.DState.pol s.DState.cons
      |> TypeLat.change_locations loc;
      s'.flow <- DStateSet.fold_left s.DState.flow StateSet.empty
        (fun flow d -> StateSet.add flow (copy_state loc d));
      s' 
    end in
  f copy_state




(* Convert an NFA (bunch of states) into a DFA (bunch of dstates) *)
let determinise old_states =
  (* DFA states correspond to sets of NFA states *)
  let module M = Map.Make (StateSet) in
  let dstates = ref M.empty in
  let rec follow p s =
    if M.mem s !dstates then
      M.find s !dstates
    else begin
      let d = fresh_dstate p in
      dstates := M.add s d !dstates;
      d.DState.cons <- TypeLat.pmap follow p (states_follow p s);
      d
    end in
  old_states |> List.iter (fun s ->
    ignore (follow s.pol (StateSet.singleton s)));
  (* flow edges:
     there should be a flow A -> B whenever there is
     a flow a -> b for a in A, b in B *)
  let dstates_containing =
    let tbl = StateTbl.create 20 in
    M.iter (fun ss d -> StateSet.iter ss (fun s -> StateTbl.add tbl s d)) !dstates;
    fun s -> StateTbl.find_all tbl s in
  let flows_to a =
    StateSet.fold_left a.flow DStateSet.empty (fun ds s ->
      DStateSet.union ds (DStateSet.of_list (dstates_containing s))) in
  !dstates |> M.iter (fun ss d ->
    d.DState.flow <- StateSet.fold_left ss DStateSet.empty (fun ds s ->
      DStateSet.union ds (flows_to s)));
  let all_dstates = !dstates |> M.bindings |> List.map snd in
  (fun s -> M.find (StateSet.singleton s) !dstates), all_dstates


(* Construct a minimal DFA using (roughly) Hopcroft's algorithm *)
let minimise dstates =
  let open DState in

  let rec check_disjoint s = function
    | [] -> ()
    | (p :: ps) ->
       assert (DStateSet.(is_empty (inter s p)));
      check_disjoint (DStateSet.union s p) ps in
    
(*
  let dump_partition ps =
    let open Format in
    ps |> List.iter (fun p ->
      printf "[%s]" (p |> DStateSet.to_list |> List.map (fun s -> string_of_int (s.id)) |> String.concat " "));
    printf "\n%!"
  in
*)
  
  (* Horrible O(n^2) initial partition *)
  let rec partition_list cmp acc = function
    | [] -> acc
    | (x :: xs) ->
       let (same, different) = List.partition (cmp x) xs in
       partition_list cmp ((x :: same) :: acc) different in

  let rec repartition cmp = function
    | [] -> []
    | (p :: ps) ->
       partition_list cmp (repartition cmp ps) p in

  let same_ctor d d' =
    let sub_ctor d1 d2 =
      assert (d1.pol = d2.pol);
      TypeLat.subs d1.pol (fun pol x y -> true) d1.cons d2.cons in
    sub_ctor d d' && sub_ctor d' d in
    

  let initial_partition = [ dstates ]
    |> repartition (fun d d' -> d.pol = d'.pol)
    |> repartition same_ctor
    |> repartition (fun d d' -> DStateSet.compare d.flow d'.flow = 0)
    |> List.map DStateSet.of_list in


  let predecessors = DStateTbl.create 20 in
  dstates |> List.iter (fun d ->
    TypeLat.iter (fun p d' -> DStateTbl.add predecessors d' d) d.pol d.cons);

  (* Find predecessors of a set ds' of dstates *)
  let pred_ctor p ds' =
    let ds = DStateSet.(fold_left ds' empty
      (fun ds d' -> union ds (of_list (DStateTbl.find_all predecessors d')))) in
    DStateSet.fold_left ds TypeLat.join_ident (fun t d ->
      TypeLat.join p (fun p x y -> DStateSet.union x y) t
        (TypeLat.pmap (fun p d' -> 
        if DStateSet.mem ds' d' then
          DStateSet.singleton d
        else DStateSet.empty) d.pol d.cons)) in

  let active = ref initial_partition in
  let rec split pol ds = function
    | [] -> []
    | p :: ps ->
       let open DStateSet in
       let p1 = inter p ds in
       let p2 = diff p ds in
       match is_empty p1, is_empty p2 with
       | false, false -> 
          let smaller = 
            if length p1 < length p2 then p1 else p2 in
          active := smaller :: !active;
          p1 :: p2 :: split pol ds ps
       | false, true 
       | true, false -> p :: split pol ds ps
       | true, true -> assert false (* p should be nonempty *) in

  let rec partition_polarity p =
    (List.hd (DStateSet.to_list p)).DState.pol in

  let rec refine ps =
    check_disjoint DStateSet.empty ps;
    (*
    dump_partition ps;*)
    match !active with
    | [] -> ps
    | (ds :: rest) ->
      active := rest;
      let pol = partition_polarity ds in
      refine (TypeLat.pfold split pol (pred_ctor pol ds) ps) in

  let remap_tbl = DStateTbl.create 20 in
  let new_dstates = initial_partition |> refine |> List.map (fun p ->
    let d = fresh_dstate (partition_polarity p) in
    DStateSet.iter p (fun x -> DStateTbl.add remap_tbl x d);
    (d, DStateSet.to_list p |> List.hd)) in

  let remap d = DStateTbl.find remap_tbl d in
  
  new_dstates |> List.iter (fun (s, d) ->
    s.cons <- TypeLat.pmap (fun p x -> remap x) d.pol d.cons;
    s.flow <- DStateSet.fold_left d.flow DStateSet.empty (fun flow x -> DStateSet.add flow (remap x)));

  remap


    
    



(* Non-deterministic entailment and subsumption *)


type antichain = (StateSet.t * StateSet.t) list ref
let antichain_new () = ref []
let antichain_ins (a : antichain) ssn ssp =
  if List.fold_left (fun b (ssn', ssp') -> b || (StateSet.subset ssn' ssn && StateSet.subset ssp' ssp) ) false !a then
    true
  else
    (a := (ssn,ssp) :: !a; false)

let common_var ssn ssp =
  let flow ss = StateSet.fold_left ss StateSet.empty (fun c s -> StateSet.union c s.flow) in
  StateSet.(not (is_empty (inter (flow ssn) ssp)))

let rec entailed a ssn ssp =
  let b = if antichain_ins a ssn ssp then true else
      common_var ssn ssp || TypeLat.lte_np (entailed a) (states_follow Neg ssn) (states_follow Pos ssp) in
(*  Printf.printf "entailment: ";
  StateSet.iter ssn (fun s -> Printf.printf "%d " s.id);
  Printf.printf "/ ";
  StateSet.iter ssp (fun s -> Printf.printf "%d " s.id);
  Printf.printf "%s\n" (match b with true -> "[Y]" | false -> "[N]"); *)
  b

let get_def tbl key def =
  if StateTbl.mem tbl key then 
    StateTbl.find tbl key 
  else
    let v = def () in
    (StateTbl.add tbl key v; v)

let rec subsumed map =
  let var_ant = StateTbl.create 20 in

  let rec subsume p ssa ssb =
    (* sum ssa <= sum ssb *)
    match p with
    | Pos -> StateSet.fold_left ssa true (fun b sa -> b && subsume_one sa ssb)
    | Neg -> StateSet.fold_left ssb true (fun b sb -> b && subsume_one sb ssa)
  and subsume_one s ssr =
    (* s+ <= ssr+ 
       or
       ssr- <= s- *)
    (* Printf.printf "%d ~ %a\n%!" s.id (fun ppf xs -> StateSet.iter xs (fun x -> Printf.fprintf ppf "%d " x.id)) ssr; *)
    StateSet.iter ssr (fun s' -> assert (s.pol = s'.pol));
    let (ssn, ssp) = match s.pol with Pos -> (StateSet.empty, ssr) | Neg -> (ssr, StateSet.empty) in
    if antichain_ins (get_def var_ant s antichain_new) ssn ssp then true else
      TypeLat.subs s.pol subsume s.cons (states_follow s.pol ssr) in

(*

                             (fun pol ssa ssb -> sub
                            StateSet.fold_left ssa true (fun b sa -> b && subsume sa ssb))
                           (fun ssa ssb ->
                            StateSet.fold_left ssb true (fun b sb -> b && subsume sa ssb))
                            
      | Pos -> cons_lte_pp (fun pol' ssa ssb -> 
        match pol' with 
        | Pos -> StateSet.fold_left ssa true (fun b sa -> b && subsume sa ssb)
        | Neg -> StateSet.fold_left ssb true (fun b sb -> b && subsume sb ssa))
        s.cons (states_follow s.pol ssr)
      | Neg -> cons_lte_nn (fun pol' ssa ssb -> 
        match pol' with
        | Pos -> StateSet.fold_left ssb true (fun b sb -> b && subsume sb ssa) 
        | Neg -> StateSet.fold_left ssa true (fun b sa -> b && subsume sa ssb))
        (states_follow s.pol ssr) s.cons in
 *)
  
  
  let ent = antichain_new () in
  let check_dataflow () = 
    (*Printf.printf "dataflow\n";*)
    StateTbl.fold (fun sp ap b -> match sp.pol with
    | Neg -> b
    | Pos -> StateSet.fold_left sp.flow b (fun b sn -> 
      if StateTbl.mem var_ant sn then
        let an = StateTbl.find var_ant sn in
        List.fold_left (fun b (_,sp') -> b && 
          List.fold_left (fun b (sn',_) -> b &&
            entailed ent sn' sp'
          ) b !an
        ) b !ap
      else b)) var_ant true in
  
  map (fun s s' -> subsume_one s (StateSet.singleton s')) &&
    check_dataflow()



let optimise_flow (roots : state list) =
  let states = find_reachable roots in
  let state_set = List.fold_left StateSet.add StateSet.empty states in
  let flows = StateTbl.create 20 in
  (* clear out all flow edges *)
  List.iter (fun s -> StateTbl.add flows s (StateSet.inter s.flow state_set);
                      s.flow <- StateSet.empty) states;
  (* re-add them in reverse postorder *)
  let antichain = antichain_new () in
  let add_flow sn sp =
    assert (sn.pol = Neg); assert (sp.pol = Pos);
    if not (entailed antichain (StateSet.singleton sn) (StateSet.singleton sp)) then
      (sn.flow <- StateSet.add sn.flow sp; sp.flow <- StateSet.add sp.flow sn) in
  let process s =
    if s.pol = Neg then
      StateSet.iter (StateTbl.find flows s) (fun sp -> add_flow s sp) in
  List.iter process (List.rev states)




type edgetype = Domain | Range

module EdgeMap = Map.Make (struct type t = edgetype let compare = compare end)

type superblock =
  { mutable blocks : block list; (* some may be empty *)
    mutable edgecounts : int StateTbl.t EdgeMap.t }

and block =
  { mutable states : StateSet.t;
    mutable size : int;
    mutable split : block;
    mutable superblock : superblock }


let refine_partition (initial_partition : StateSet.t list) (back_edges : StateSet.t StateTbl.t EdgeMap.t) =
  let count_mod (t : int StateTbl.t) (s : state) (k : int) =
    if not (StateTbl.mem t s) then StateTbl.add t s 0;
    let n = StateTbl.find t s + k in
    assert (n >= 0);
    if n = 0 then StateTbl.remove t s else StateTbl.replace t s n in
  
  let initial_superblock = { blocks = []; edgecounts = EdgeMap.map (fun edges ->
    let t = StateTbl.create 20 in
    StateTbl.iter (fun y ss ->
      StateSet.iter ss (fun x -> count_mod t x 1)) edges; t) back_edges } in

  let block_of_state : block StateTbl.t = StateTbl.create 20 in

  let initial_blocks = List.map (fun states ->
    let rec b = { states; size = StateSet.length states;
                  split = b; superblock = initial_superblock } in
    StateSet.iter states (fun s -> StateTbl.add block_of_state s b); 
    b) initial_partition in
  initial_superblock.blocks <- initial_blocks;

  
  (* Step 4 of Paige & Tarjan *)
  let split_blocks (set : StateSet.t) (compound_blocks : superblock list) : superblock list =
    (* Find the partition blocks b that have a nonempty intersection with set,
       and split them into (b & set) and (b - set) *)
    let new_blocks =
      StateSet.fold_left set [] (fun bs x ->
        let b = StateTbl.find block_of_state x in
        let bs = 
          if b.split != b then bs else begin
            let diff_states = StateSet.diff b.states set in
            let inter_states = StateSet.inter b.states set in
            let b' = { states = inter_states; 
                       size = StateSet.length inter_states;
                       split = b;
                       superblock = b.superblock } in
            b.states <- diff_states;
            b.size <- b.size - b'.size;
            b.split <- b';
            b.split :: bs
          end in
        StateTbl.replace block_of_state x b.split;
        bs) in
    (* reset the split fields and find any newly-compound superblocks *)
    List.fold_left (fun compound_blocks b -> 
      let b' = b.split in
      assert (b' != b && b'.split == b);
      assert (b'.superblock == b.superblock);
      b.split <- b; b'.split <- b';
      b.superblock.blocks <- b' :: b.superblock.blocks;
      match b.superblock.blocks with
      | [a; b] -> b.superblock :: compound_blocks (* this block has just become compound *)
      | _ -> compound_blocks) compound_blocks new_blocks in
  
    
  let refine_by_block (b : block) (compound_blocks : superblock list) =
    let orig_superblock = b.superblock in
    let edgecounts = EdgeMap.map (fun edges ->
      let t = StateTbl.create 20 in
      StateSet.iter b.states (fun y ->
        StateSet.iter (StateTbl.find edges y) (fun x ->
          count_mod t x 1)); t) back_edges in
    b.superblock <- { blocks = [b]; edgecounts };
    EdgeMap.fold (fun etype edges compound_blocks ->
      (* Calculate E^-1(B) *)
      let back_b = StateTbl.fold (fun s _ bb -> StateSet.add bb s) edges StateSet.empty in
      (* Calculate E^-1(B) - E^-1(S - B) *)
      let orig_edgecounts = EdgeMap.find etype orig_superblock.edgecounts in
      let back_bsb = StateTbl.fold (fun s countB bb ->
        let countS = StateTbl.find orig_edgecounts s in
        if countB = countS then StateSet.add bb s else bb) edges StateSet.empty in
      (* Update counts *)
      StateTbl.iter (fun s countB ->
        count_mod orig_edgecounts s (-countB)) edges;
      split_blocks back_bsb (split_blocks back_b compound_blocks))
      edgecounts compound_blocks in
  
  
  let rec refine_loop = function
    | [] -> ()
    | s :: compound_blocks -> first_block compound_blocks s.blocks
  and first_block compound_blocks = function
    | [] -> refine_loop compound_blocks
    | b0 :: rest when b0.size == 0 -> first_block compound_blocks rest
    | b0 :: rest -> second_block compound_blocks b0 rest
  and second_block compound_blocks b0 = function
    | [] -> refine_loop compound_blocks
    | b1 :: rest when b1.size == 0 -> second_block compound_blocks b0 rest
    | b1 :: rest ->
      assert (b0.superblock == b1.superblock);
      let s = b0.superblock in
      let b =
        if b0.size < b1.size then
          (s.blocks <- b1 :: rest; b0)
        else
          (s.blocks <- b0 :: rest; b1) in
      refine_loop (refine_by_block b compound_blocks) in
  refine_loop [initial_superblock];

  let res = StateTbl.create 20 in
  StateTbl.iter (fun s b -> StateTbl.add res s (StateSet.min_elt b.states)) block_of_state;
  res
