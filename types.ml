type polarity = Pos | Neg

let polneg = function Pos -> Neg | Neg -> Pos
let polmul = function Pos -> (fun p -> p) | Neg -> polneg

type 'a constructed =
| Top
| Unit
| Func of 'a * 'a
| Bot

let cons_lte_p f a b =
  match a, b with
  | Bot, _ -> true
  | _, Top -> true
  | Unit, Unit -> true
  | Func(d,r), Func(d',r') -> f Neg d' d && f Pos r r'
  | _, _ -> false

let cons_lte f a b = cons_lte_p (fun p a b -> f a b) a b



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
  



type var = string

type 'a typeterm = 
| TVar of 'a
| TCons of ('a typeterm) constructed
| TAdd of 'a typeterm * 'a typeterm
| TRec of 'a * 'a typeterm

let string_of_var v = v
(*  if v < 26 then String.make 1 (Char.chr (Char.code 'a' + v)) else Printf.sprintf "v_%d" (v - 26) *)

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
      mutable cons : StateSet.t constructed;
      mutable flow : StateSet.t }
end = struct
  type state =
    { id : state_id;
      pol : polarity;
      mutable cons : StateSet.t constructed;
      mutable flow : StateSet.t }
end
and StateSet : Intmap.S with type elt = State.state = Intmap.Fake (struct type t = State.state let get_id = State.(fun s -> s.id) end)

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
  cons_join p merge x y

let merge s s' =
  assert (s.pol = s'.pol);
  s.cons <- state_cons_join s.pol s.cons s'.cons;
  s.flow <- StateSet.union s.flow s'.flow;
  StateSet.iter s.flow (fun s' -> assert (s'.pol <> s.pol))


let next_id = ref 0


(* FIXME: Incorrect for negative recursion *)
let compile_terms (map : (polarity -> var typeterm -> state) -> 'a) : 'a =
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
    | TCons c -> mkstate p (cons_map p (fun p t -> StateSet.singleton (compile r p t)) c) 
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

let print_automaton ppf (root : state) =
  let dumped = StateTbl.create 20 in
  let pstate ppf s = fprintf ppf "n%d" s.id in
  let rec dump s =
    if StateTbl.mem dumped s then () else begin
      StateTbl.add dumped s s;
      fprintf ppf "%a [label=\"%s (%d)\"];\n" pstate s (cons_name s.cons) s.id;
      List.iter (fun (f, ss') -> 
        StateSet.iter ss'
          (fun s' -> 
            fprintf ppf "%a -> %a [label=\"%s\"];\n" pstate s pstate s' f;
            dump s'))
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
        fprintf ppf "%a -> %a [style=dashed, constraint=false]\n" pstate s pstate s'
      with Not_found -> ())) dumped;
  fprintf ppf "}\n"

let rec find_reachable (root : state) =
  let states = StateTbl.create 20 in
  let rec search s =
    if StateTbl.mem states s then () else begin
      StateTbl.add states s ();
      List.iter
        (fun (f, ss') -> StateSet.iter ss' search)
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
let decompile_automaton (root : state) : var typeterm =
  let states = find_reachable root in
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
    StateSet.fold_left states (0, StateSet.empty, StateSet.empty)
      (fun ((best_n, _, _) as best) s ->
        let (ss, ss') = principal_biclique s in
        let n = StateSet.(length ss + length ss') in
        if n > best_n then (n, ss, ss') else best) in
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
  let fresh_var = let var_id = ref (-1) in fun () -> incr var_id; "v" ^ string_of_int !var_id in
  let state_vars = StateTbl.create 20 in
  List.iter (fun (ss, ss') -> 
    let v = TVar (fresh_var ()) in
    let iter ss = StateSet.iter ss (fun s -> StateTbl.add state_vars s v) in
    iter ss; iter ss') biclique_decomposition;


  let rec term_add p = function
    | [] -> TCons (pol_ident p)
    | [t] -> t
    | (t :: ts) ->
      if t = TCons (pol_ident p) then term_add p ts else
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
      let t = cons_map s.pol (fun p' ss' -> term_add p' (List.map decompile (StateSet.to_list ss'))) s.cons in
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
    if Hashtbl.mem seen (sp.id, sn.id) then true
    else begin
      Hashtbl.add seen (sp.id, sn.id) ();
      StateSet.iter sn.flow (fun s -> merge s sp);
      StateSet.iter sp.flow (fun s -> merge s sn);
      cons_lte closure_l sp.cons sn.cons
    end
  and closure_l ssp ssn =
    StateSet.fold_left ssp true (fun b sp ->
      b && StateSet.fold_left ssn true (fun b sn ->
        b && closure sp sn)) in
  closure sp_orig sn_orig


type antichain = (StateSet.t * StateSet.t) list ref
let antichain_new () = ref []
let antichain_ins (a : antichain) ssn ssp =
  if List.fold_left (fun b (ssn', ssp') -> b || (StateSet.subset ssn' ssn && StateSet.subset ssp' ssp) ) false !a then
    true
  else
    (a := (ssn,ssp) :: !a; false)


let rec expand_flow sn sp =
  Printf.printf "expanding flow %d %d\n" sn.id sp.id;
  assert (sn.pol = Neg);
  assert (sp.pol = Pos);
  sn.flow <- StateSet.add sn.flow sp;
  sp.flow <- StateSet.add sp.flow sn;
  ignore (cons_join Pos (fun p a b ->
    match p with
    | Pos -> expand_flows a b; StateSet.empty
    | Neg -> expand_flows b a; StateSet.empty) sn.cons sp.cons)
and expand_flows ssn ssp =
  StateSet.iter ssn (fun sn -> StateSet.iter ssp (fun sp -> expand_flow sn sp))

let expand_all_flow s =
  StateSet.iter (find_reachable s) (fun s -> 
    if s.pol = Neg then StateSet.iter s.flow (fun s' -> expand_flow s s'))
  
    

let states_follow p (s : StateSet.t) : StateSet.t constructed =
  StateSet.fold_left s (pol_ident p) (fun c s -> cons_join p (fun p a b -> StateSet.union a b) c s.cons)

let common_var ssn ssp =
  let flow ss = StateSet.fold_left ss StateSet.empty (fun c s -> StateSet.union c s.flow) in
  StateSet.(not (is_empty (inter (flow ssn) ssp)))

let rec entailed a ssn ssp =
  let b = if antichain_ins a ssn ssp then true else
      common_var ssn ssp || cons_lte (entailed a) (states_follow Neg ssn) (states_follow Pos ssp) in
  Printf.printf "entailment: ";
  StateSet.iter ssn (fun s -> Printf.printf "%d " s.id);
  Printf.printf "/ ";
  StateSet.iter ssp (fun s -> Printf.printf "%d " s.id);
  Printf.printf "%s\n" (match b with true -> "[Y]" | false -> "[N]");
  b

let get_def tbl key def =
  if StateTbl.mem tbl key then 
    StateTbl.find tbl key 
  else
    let v = def () in
    (StateTbl.add tbl key v; v)

let rec subsumed map =
  let var_ant = StateTbl.create 20 in

  let rec subsume s ssr =
    (* s+ <= ssr+ 
       or
       ssr- <= s- *)
    StateSet.iter ssr (fun s' -> assert (s.pol = s'.pol));
    let (ssn, ssp) = match s.pol with Pos -> (StateSet.empty, ssr) | Neg -> (ssr, StateSet.empty) in
    if antichain_ins (get_def var_ant s antichain_new) ssn ssp then true else
      match s.pol with
      | Pos -> cons_lte_p (fun pol' ssa ssb -> 
        match pol' with 
        | Pos -> StateSet.fold_left ssa true (fun b sa -> b && subsume sa ssb)
        | Neg -> StateSet.fold_left ssb true (fun b sb -> b && subsume sb ssa))
        s.cons (states_follow s.pol ssr)
      | Neg -> cons_lte_p (fun pol' ssa ssb -> 
        match pol' with
        | Pos -> StateSet.fold_left ssb true (fun b sb -> b && subsume sb ssa) 
        | Neg -> StateSet.fold_left ssa true (fun b sa -> b && subsume sa ssb))
        (states_follow s.pol ssr) s.cons in
  
  let ent = antichain_new () in
  let check_dataflow () = 
    Printf.printf "dataflow\n";
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
  
  map (fun s s' -> subsume s (StateSet.singleton s')) &&
    check_dataflow()


;;
(*
let term = (TCons (Func (TVar 1, TAdd (TVar 2, TVar 1)))) ;;

let term = TRec (2, TAdd (TVar 1, TAdd (TVar 2, TCons (Func (TVar 1, TVar 1))))) ;;

let term = (TCons (Func (TVar 1, TCons (Func (TVar 2, TAdd (TVar 1, TVar 2))))));;
*)

(*
let kpair a b = TCons (Func (TCons (Func (a, TCons (Func (b, TCons Unit)))), TCons Unit))
let term = (TCons (Func (TVar 1, TCons (Func (TVar 2, kpair (TVar 1) (TVar 2))))));;
let term = (TCons (Func (TVar "1", TCons (Func (TVar "2", kpair (TAdd (TVar "1", TVar "1")) (TAdd (TVar "1", TVar "2")))))));;

let term = (TCons (Func (TVar 1, TCons (Func (TVar 1, kpair (TVar 1) (TVar 1))))));;



fprintf err_formatter "%a@." (print_typeterm Pos) term;;
fprintf err_formatter "%a@." (print_typeterm Pos) (decompile_automaton (compile_term term));;
printf "%a" print_automaton (compile_term term);;

*)
