type polarity = Pos | Neg

let polneg = function Pos -> Neg | Neg -> Pos
let polmul = function Pos -> (fun p -> p) | Neg -> polneg

type 'a constructed =
| Top
| Unit
| Func of 'a * 'a
| Bot

let cons_lte f a b =
  match a, b with
  | Bot, _ -> true
  | _, Top -> true
  | Unit, Unit -> true
  | Func(d,r), Func(d',r') -> f d' d && f r r'
  | _, _ -> false

let cons_join pol f a b =
  match pol with
  | Pos -> begin (* least upper bound *)
    match a, b with
    | Top, _ | _, Top -> Top
    | Bot, x | x, Bot -> x
    | Unit, Unit -> Unit
    | Func (d,r), Func (d',r') -> 
      Func (f (polneg pol) d d', f pol r r')
    | Unit, Func(_,_) | Func(_,_), Unit -> Top
  end
  | Neg -> begin (* greatest lower bound *)
    match a, b with
    | Bot, _ | _, Bot -> Bot
    | Top, x | x, Top -> x
    | Unit, Unit -> Unit
    | Func (d, r), Func (d', r') -> 
      Func (f (polneg pol) d d', f pol r r')
    | Unit, Func(_, _) | Func(_,_), Unit -> Bot
  end

let cons_name = function
  | Top -> "Top"
  | Unit -> "unit"
  | Func(_,_) -> "->"
  | Bot -> "Bot"

let cons_fields = function
  | Func (d, r) -> ["d", d; "r", r]
  | _ -> []

let pol_ident = function Pos -> Bot | Neg -> Top

let cons_map p f = function
  | Top -> Top
  | Unit -> Unit
  | Func (d, r) -> Func (f (polneg p) d, f p r)
  | Bot -> Bot
  



type var = int

type 'a typeterm = 
| TVar of 'a
| TCons of ('a typeterm) constructed
| TAdd of 'a typeterm * 'a typeterm
| TRec of 'a * 'a typeterm

let string_of_var v =
  if v < 26 then String.make 1 (Char.chr (Char.code 'a' + v)) else Printf.sprintf "v_%d" (v - 26)

open Format

let rec gen_print_typeterm vstr pol ppf = function 
  | TVar v -> fprintf ppf "%s" (vstr v)
  | TCons (Func (t1, t2)) ->
    fprintf ppf "@[(%a ->@ %a)@]" (gen_print_typeterm vstr (polneg pol)) t1 (gen_print_typeterm vstr pol) t2
  | TCons Top -> fprintf ppf "Top"
  | TCons Bot -> fprintf ppf "Bot"
  | TCons Unit -> fprintf ppf "unit"
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
      mutable cons : state list constructed;
      mutable flow : StateSet.t }
end = struct
  type state =
    { id : state_id;
      pol : polarity;
      mutable cons : state list constructed;
      mutable flow : StateSet.t }
end
and StateSet : Intmap.S with type elt = State.state = Intmap.Make (struct type t = State.state let get_id (s : t) = s.id end)

open State

module StateHash = struct type t = state let equal x y = x == y let hash x = x.id end
module StateTbl = Hashtbl.Make (StateHash)

module VarOrd = struct type t = var let compare = compare end
module VarMap = Map.Make (VarOrd)

let state_cons_join p x y =
  let merge p x y = StateSet.(to_list (union (of_list x) (of_list y))) in
  cons_join p merge x y

(* FIXME: Incorrect for negative recursion *)
let compile_term (t : var typeterm) : state =
  let next_id = ref 0 in
  let states = ref [] in
  let mkstate pol cons = 
    let r = { id = !next_id; pol; cons; flow = StateSet.empty} in 
    (states := r :: !states; incr next_id; r) in
  let state_vars = StateTbl.create 20 in
  let epsilon_trans = StateTbl.create 20 in
  let rec compile r p = function
    | TVar v -> (
      try VarMap.find v r
      with Not_found ->
        (let s = mkstate p (pol_ident p) in
         StateTbl.add state_vars s v; s))
    | TCons c -> mkstate p (cons_map p (fun p t -> [compile r p t]) c) 
    | TAdd (t1, t2) ->
      let s1, s2 = compile r p t1, compile r p t2 in
      let s = mkstate p (pol_ident p) in
      StateTbl.add epsilon_trans s s1;
      StateTbl.add epsilon_trans s s2;
      s
    | TRec (v, t) ->
      let s = mkstate p (pol_ident p) in
      let s' = compile (VarMap.add v s r) p t in
      StateTbl.add epsilon_trans s s';
      s in
  let root = compile VarMap.empty Pos t in

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

let print_automaton ppf (root : state) =
  let dumped = StateTbl.create 20 in
  let pstate ppf s = fprintf ppf "n%d" s.id in
  let rec dump s =
    if StateTbl.mem dumped s then () else begin
      StateTbl.add dumped s s;
      fprintf ppf "%a [label=\"%s\"];\n" pstate s (cons_name s.cons);
      List.iter (fun (f, ss') -> 
        List.iter (fun s' -> 
          fprintf ppf "%a -> %a [label=\"%s\"];\n" pstate s pstate s' f;
          dump s') ss')
        (cons_fields s.cons)
    end in
  fprintf ppf "digraph {\n";
  (* dump structural constraints *)
  dump root;
  (* dump dataflow constraints *)
  StateTbl.iter (fun s _ ->
    if s.pol = Neg then StateSet.iter s.flow (fun s' -> 
      try
        let s' = StateTbl.find dumped s' in
        fprintf ppf "%a -> %a [style=dashed]\n" pstate s pstate s'
      with Not_found -> ())) dumped;
  fprintf ppf "}\n"

let rec find_reachable (root : state) =
  let states = StateTbl.create 20 in
  let rec search s =
    if StateTbl.mem states root then () else begin
      StateTbl.add states s ();
      List.iter
        (fun (f, ss') -> List.iter search ss')
      (cons_fields s.cons)
    end in
  search root;
  StateTbl.fold (fun s _ m -> StateSet.add m s) states StateSet.empty

let garbage_collect (root : state) =
  let states = find_reachable root in
  StateSet.iter states (fun s -> s.flow <- StateSet.inter s.flow states)

let make_table s f =
  let t = StateTbl.create 20 in
  StateSet.iter s (fun s -> StateTbl.add t s (f s)); 
  t

(* FIXME: deterministic? ID-dependent? *)
let decompile_automaton (root : state) =
  let states = find_reachable root in
  let state_flow = make_table states (fun s -> StateSet.inter states s.flow) in

  (* Decompose flow constraints into variables.
     This is the biclique decomposition of a bipartite graph. Doing it optimally
     is NP-complete, we do it badly in polynomial time *)
  let principal_biclique s = 
    let ss' = StateTbl.find state_flow s in
    if StateSet.is_empty ss' then StateSet.(empty, empty) else begin
      let ss = StateSet.fold_left ss' states
        (fun s' m -> StateSet.inter s'.flow m) in
      fprintf err_formatter "%d %d\n" (StateIdSet.cardinal ss) (StateIdSet.cardinal ss');
      (ss, ss') 
    end in
  let find_biclique () =
    StateSet.fold_left states (0, StateSet.empty, StateSet.empty)
      (fun ((best_n, _, _) as best) s ->
        let (ss, ss') = principal_biclique s in
        let n = StateSet.(length ss + length ss') in
        if n > best_n then (n, ss, ss') else best)
      states (0, StateSet.empty, StateSet.empty) in
  let del_biclique ss ss' =
    let del ss ss' = 
      StateSet.iter ss (fun sid -> 
        StateIdTbl.replace state_flow sid 
          (StateIdSet.diff (StateIdTbl.find state_flow sid) ss')) ss in
    del ss ss'; del ss' ss in
  let rec find_biclique_decomposition () =
    let (n, ss, ss') = find_biclique () in
    fprintf err_formatter "%d\n" n;
    if n = 0 then [] else begin
      del_biclique ss ss';
      (ss, ss') :: find_biclique_decomposition ()
    end in
  let biclique_decomposition = find_biclique_decomposition () in

  (* Each biclique in the decomposition corresponds to a variable *)
  let fresh_var = let var_id = ref (-1) in fun () -> incr var_id; !var_id in
  let state_vars = StateIdTbl.create 20 in
  List.iter (fun (ss, ss') -> 
    let v = TVar (fresh_var ()) in
    let iter ss = StateIdSet.iter (fun s -> StateIdTbl.add state_vars s v) ss in
    iter ss; iter ss') biclique_decomposition;


  let rec term_add p = function
    | [] -> TCons (pol_ident p)
    | [t] -> t
    | (t :: ts) ->
      if t = TCons (pol_ident p) then term_add p ts else
        TAdd (t, term_add p ts) in

  let rec decompile r s =
    if StateMap.mem s r then
      let visited = StateMap.find s r in
      match !visited with
      | Some v -> TVar v
      | None -> let v = fresh_var () in (visited := Some v; TVar v)
    else
      let vars = StateIdTbl.find_all state_vars s.id in
      let visited = ref None in
      let r' = StateMap.add s visited r in
      let t = cons_map s.pol (fun p' ss' -> term_add p' (List.map (decompile r') ss')) s.cons in
      let tv = term_add s.pol (TCons t :: vars) in
      match !visited with
      | None -> tv
      | Some v -> TRec (v, tv) in
  decompile StateMap.empty root
  

let rec tensor_contraction states stateset sp sn =
  let merge s s' =
    assert (s.pol = s'.pol);
    s.cons <- state_cons_join s.pol s.cons s'.cons;
    s.flow <- StateIdSet.union s.flow s'.flow in
  let iter_set f ss =
    StateIdSet.iter (fun sid -> f (StateIdTbl.find states sid)) (StateIdSet.inter ss stateset) in
  let seen = Hashtbl.create 20 in
  let rec closure sp sn =
    if Hashtbl.mem seen (sp, sn) then true
    else begin
      Hashtbl.add seen (sp, sn) ();
      assert (sp.pol = Pos);
      assert (sn.pol = Neg);
      iter_set (fun s -> merge s sp) sn.flow;
      iter_set (fun s -> merge s sn) sp.flow;
      cons_lte closure_l sp.cons sn.cons
    end
  and closure_l ssp ssn =
    List.fold_left (fun b sp -> 
      if b then List.fold_left (fun b sn ->
        if b then closure sp sn else false) true ssn
      else false) true ssp in
  closure sp sn
  

;;
(*
let term = (TCons (Func (TVar 1, TAdd (TVar 2, TVar 1)))) ;;

let term = TRec (2, TAdd (TVar 1, TAdd (TVar 2, TCons (Func (TVar 1, TVar 1))))) ;;

let term = (TCons (Func (TVar 1, TCons (Func (TVar 2, TAdd (TVar 1, TVar 2))))));;
*)

let kpair a b = TCons (Func (TCons (Func (a, TCons (Func (b, TCons Unit)))), TCons Unit))
let term = (TCons (Func (TVar 1, TCons (Func (TVar 2, kpair (TVar 1) (TVar 2))))));;
let term = (TCons (Func (TVar 1, TCons (Func (TVar 2, kpair (TAdd (TVar 1, TVar 1)) (TAdd (TVar 1, TVar 2)))))));;
(*
let term = (TCons (Func (TVar 1, TCons (Func (TVar 1, kpair (TVar 1) (TVar 1))))));;
*)


fprintf err_formatter "%a@." (print_typeterm Pos) term;;
fprintf err_formatter "%a@." (print_typeterm Pos) (decompile_automaton (compile_term term));;
printf "%a" print_automaton (compile_term term);;

