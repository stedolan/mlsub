type polarity = Pos | Neg

let polneg = function Pos -> Neg | Neg -> Pos
let polmul = function Pos -> (fun p -> p) | Neg -> polneg


(*

0
unit
a -> b
unit + (a -> b)


Object types:

hasA * A ??

{ a : t1 } | { b : t2 } = {}

{ a : t1 } | { b : t2 } = {}

{ a : t1 } <: {}

[ {a : t1} ] = -b + fa*[t1] + fb*T
[ {b : t2} ] = -a + fb*[t2] + fa*T
[ {a : t1} | {b : t2} ] = -a + -b + fa*T + fb*T
[ {a : t1} & {b : t2} ] = fa*[t1] + fb*[t2]
[ {} ] = -a + -b + fa*T + fb*T


{} <: { a : t1 } | { b : t2 }



{ a : t1 } & { b : t2 } = { a : t1, b : t2 }

*)


type 'a t_unit = unit
let t_unit_join p f () () = ()
let t_unit_lte f x y = true
let t_unit_subs f pol () () = true

type 'a t_fun = Func of 'a * 'a
let t_fun_join p f (Func (d,r)) (Func (d',r')) = Func (f (polneg p) d d', f p r r')
let t_fun_lte f (Func (d, r)) (Func (d', r')) = f d' d && f r r'
let t_fun_subs f pol (Func (d, r)) (Func (d', r')) = f (polneg pol) d' d && f pol r r'

let opt_join j p f x y = 
  match x,y with
  | None, None -> None
  | (None, r) | (r, None) -> r
  | (Some x, Some y) -> Some (j p f x y)

type 'a constructed = Cons of ('a t_unit option) * ('a t_fun option)

let cons_join p f (Cons (ux, fx)) (Cons (uy, fy)) =
  Cons
    (opt_join t_unit_join p f ux uy,
     opt_join t_fun_join p f fx fy)

let cons_lte_pn f x y =
  match x, y with
  | Cons (None, None), _ -> true
  | Cons _, Cons (None, None) -> true
  | Cons (None, Some x), Cons (None, Some y) -> t_fun_lte f x y
  | Cons (Some x, None), Cons (Some y, None) -> t_unit_lte f x y
  | _, _ -> false

let opt_lte_np l f x y =
  match x, y with
  | Some x, Some y -> l f x y
  | _, _ -> false

let cons_lte_np f (Cons (ux, fx)) (Cons (uy, fy)) =
  opt_lte_np t_unit_lte f ux uy ||
    opt_lte_np t_fun_lte f fx fy

let opt_lte_pp l f pol x y =
  match x, y with
  | Some x, Some y -> l f pol x y
  | None, _ -> true
  | Some _, None -> false

let cons_lte_subs f pol (Cons (ux, fx)) (Cons (uy, fy)) =
  opt_lte_pp t_unit_subs f pol ux uy &&
    opt_lte_pp t_fun_subs f pol fx fy

let cons_map p f = function
  | Cons (u, Some (Func (d, r))) -> Cons (u, Some (Func (f (polneg p) d, f p r)))
  | Cons (u, None) -> Cons (u, None)

let cons_name = function
  | Cons (None, None) -> "0"
  | Cons (Some _, None) -> "unit"
  | Cons (None, Some _) -> "->"
  | Cons (Some _, Some _) -> "unit + fun"

let cons_fields = function
  | Cons (_, Some (Func (d, r))) -> ["d", d; "r", r]
  | _ -> []

let pol_ident p = Cons (None, None)
  



type var = string

type 'a typeterm = 
| TVar of 'a
| TCons of ('a typeterm) constructed
| TAdd of 'a typeterm * 'a typeterm
| TRec of 'a * 'a typeterm


let ty_unit = TCons (Cons (Some (), None))
let ty_fun d r = TCons (Cons (None, Some (Func (d, r))))
let ty_zero = TCons (Cons (None, None))
                       
let string_of_var v = v
(*  if v < 26 then String.make 1 (Char.chr (Char.code 'a' + v)) else Printf.sprintf "v_%d" (v - 26) *)

open Format

let rec gen_print_typeterm vstr pol ppf = function 
  | TVar v -> fprintf ppf "%s" (vstr v)
  | TCons (Cons (None, Some (Func (t1, t2)))) ->
    fprintf ppf "@[(%a ->@ %a)@]" (gen_print_typeterm vstr (polneg pol)) t1 (gen_print_typeterm vstr pol) t2
  | TCons (Cons (Some (), None)) ->
     fprintf ppf "unit"
  | TCons (Cons (Some u, Some f)) ->
     gen_print_typeterm vstr pol ppf (TAdd (TCons (Cons (Some u, None)), TCons (Cons (None, Some f))))
  | TCons (Cons (None, None)) ->
     fprintf ppf "%s" (match pol with Pos -> "Bot" | Neg -> "Top")
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
  cons_join p merge x y

let merge s s' =
  assert (s.pol = s'.pol);
  s.cons <- state_cons_join s.pol s.cons s'.cons;
  s.flow <- StateSet.union s.flow s'.flow;
  StateSet.iter s.flow (fun s' -> assert (s'.pol <> s.pol))


let next_id = ref 0


(* FIXME: Does not detect negative recursion *)
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

                
let fresh_id_counter = ref 1000
let fresh_id () =
  let n = !fresh_id_counter in incr fresh_id_counter; n

let clone f =
  let states = StateTbl.create 20 in
  let rec copy_state s =
    if StateTbl.mem states s then StateTbl.find states s else
      let s' = { id = fresh_id ();
                 pol = s.pol;
                 cons = Cons (None, None);
                 flow = StateSet.empty } in
      StateTbl.add states s s';
      List.iter
        (fun (f, ss') -> StateSet.iter ss' (fun s -> ignore (copy_state s)))
        (cons_fields s.cons);
      StateSet.iter s.flow (fun s -> ignore (copy_state s));
      s' in
  let r = f copy_state in
  let remap_states ss = StateSet.fold_left ss StateSet.empty
        (fun ss' s -> StateSet.add ss' (StateTbl.find states s)) in
  StateTbl.iter (fun s_old s_new -> 
    s_new.cons <- cons_map s_old.pol (fun p ss -> remap_states ss) s_old.cons;
    s_new.flow <- remap_states s_old.flow) states;
  r

                
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
      cons_lte_pn closure_l sp.cons sn.cons
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
      common_var ssn ssp || cons_lte_np (entailed a) (states_follow Neg ssn) (states_follow Pos ssp) in
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

  let rec subsume p ssa ssb =
    (* sum ssa <= sum ssb *)
    match p with
    | Pos -> StateSet.fold_left ssa true (fun b sa -> b && subsume_one sa ssb)
    | Neg -> StateSet.fold_left ssb true (fun b sb -> b && subsume_one sb ssa)
  and subsume_one s ssr =
    (* s+ <= ssr+ 
       or
       ssr- <= s- *)
    Printf.printf "%d ~ %a\n%!" s.id (fun ppf xs -> StateSet.iter xs (fun x -> Printf.fprintf ppf "%d " x.id)) ssr;
    StateSet.iter ssr (fun s' -> assert (s.pol = s'.pol));
    let (ssn, ssp) = match s.pol with Pos -> (StateSet.empty, ssr) | Neg -> (ssr, StateSet.empty) in
    if antichain_ins (get_def var_ant s antichain_new) ssn ssp then true else
      cons_lte_subs subsume s.pol s.cons (states_follow s.pol ssr) in

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
  
  map (fun s s' -> subsume_one s (StateSet.singleton s')) &&
    check_dataflow()







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
