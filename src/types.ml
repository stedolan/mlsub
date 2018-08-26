open Typector
open Variance
open Exp

(* Lattice of types as coproduct *)

let rec ty_add p ts = ts
  |> List.filter (function
     | TZero p' when p = p' -> false
     | _ -> true)
  |> function
    | [] -> TZero p
    | [t] -> t
    | (t :: ts) -> TAdd (p, t, ty_add p ts)

module TypeLat = struct
  type 'a t =
    | LZero
    | LUnexpanded of 'a Components.t    (* must be a type alias *)
    | LExpanded of 'a Components.t list (* nonempty list, never includes type aliases *)

  let lift t =
    if get_stamp t = builtin_stamp then
      LExpanded [t]
    else
      LUnexpanded t

  let as_list = function
    | LZero -> []
    | LUnexpanded t -> [t]
    | LExpanded ts -> ts

  let of_list = function
    | [] -> LZero
    | [t] -> 
       if Typector.get_stamp t = builtin_stamp
       then LExpanded [t]
       else LUnexpanded t
    | ts -> 
       (List.iter (fun t -> 
         assert (Typector.get_stamp t = builtin_stamp)) ts;
        LExpanded ts)

  let pmap f pol = function
    | LZero -> LZero
    | LUnexpanded t -> LUnexpanded (Components.pmap f pol t)
    | LExpanded t -> LExpanded (List.map (Components.pmap f pol) t)

  let pfold_comps f pol t x =
    List.fold_right (Components.pfold f pol) t x
      
  let rec pfold f pol ty x = match ty with
    | LZero -> x
    | LUnexpanded t -> Components.pfold f pol t x
    | LExpanded t -> pfold_comps f pol t x

  let iter f p x = pfold (fun pol x r -> f pol x) p x ()

  let rec join_comps pol f xs ys = match xs with
    | [] -> ys
    | x :: xs ->
       match List.partition (Components.cmp_component x) ys with
       | [], ys -> x :: join_comps pol f xs ys
       | [y], ys -> Components.join pol f x y :: join_comps pol f xs ys
       | y1 :: y2 :: _, _ -> failwith "two terms in same component"

  let join_ident = LZero


  let rec subs_comps pol f xs ys =
    (* lub X <= lub Y or glb X >= glb Y *)
    match xs with
    | [] -> true
    | x :: xs -> match List.partition (Components.cmp_component x) ys with
      | [], ys -> false
      | [y], ys ->
         (match pol with
         | Pos -> Components.lte' (fun p x y -> f p x y) x y
         | Neg -> Components.lte' (fun p y x -> f (polneg p) x y) y x)
         && subs_comps pol f xs ys
      | y1 :: y2 :: _, _ -> failwith "two terms in same component"

  let list_fields = function
    | LZero -> []
    | LUnexpanded x -> Components.list_fields x
    | LExpanded x -> x |> List.map Components.list_fields |> List.concat

  let to_typeterm pol = function
    | LZero -> TZero pol
    | LUnexpanded t -> TCons t
    | LExpanded t -> ty_add pol (List.map (fun t -> TCons t) t)

  let change_locations l = fun x -> x (* function
    | LZero -> LZero
    | LUnexpanded t -> LUnexpanded (Components.change_locations l t)
    | LExpanded t -> LExpanded (List.map (Components.change_locations l) t)*)
end



  



(* Automata *)


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

type rawstate = State.state

module StateHash = struct type t = State.state let equal x y = x == y let hash x = x.id end
module StateTbl = Hashtbl.Make (StateHash)

module VarOrd = struct type t = tyvar let compare = compare end
module VarMap = Map.Make (VarOrd)


let check_polarity s =
  StateSet.iter s.flow (fun s' -> assert (s'.pol <> s.pol));
  TypeLat.iter (fun p ss -> StateSet.iter ss (fun s -> assert (p = s.pol))) s.pol s.cons

let fresh_id_counter = ref 0
let fresh_id () =
  let n = !fresh_id_counter in incr fresh_id_counter; n

let mkstate pol cons flow =
  { id = fresh_id (); pol; cons; flow }

let cons pol (t : rawstate Components.t) : rawstate =
  { id = fresh_id ();
    pol;
    cons = TypeLat.lift (Components.pmap (fun p s -> assert (s.pol = p); StateSet.singleton s) pol t);
    flow = StateSet.empty }

let flow_pair () =
  let pos =
    { id = fresh_id (); pol = Pos; cons = TypeLat.join_ident; flow = StateSet.empty } in
  let neg =
    { id = fresh_id (); pol = Neg; cons = TypeLat.join_ident; flow = StateSet.empty } in
  pos.flow <- StateSet.singleton neg;
  neg.flow <- StateSet.singleton pos;
  (neg, pos)

let zero p =
  mkstate p TypeLat.join_ident StateSet.empty


let rec expand_both expa (pa : polarity) ca expb (pb : polarity) cb = let open TypeLat in
  match ca, cb with
  | LZero, b -> LZero, b
  | a, LZero -> a, LZero
  | (LExpanded _ as a), (LExpanded _ as b) ->
     a, b
  | LUnexpanded a, LUnexpanded b ->
     let sta = get_stamp a and stb = get_stamp b in
     if sta = stb then
       if sta = builtin_stamp then
         LExpanded [a], LExpanded [b]
       else
         LUnexpanded a, LUnexpanded b
     else
       if sta < stb then
         expand_both expa pa ca expb pb (b |> expand_alias |> expb pb)
       else
         expand_both expa pa (a |> expand_alias |> expa pa) expb pb cb
  | (LExpanded _ as a), LUnexpanded b ->
     expand_both expa pa a expb pb (b |> expand_alias |> expb pb)
  | LUnexpanded a, (LExpanded _ as b) ->
     expand_both expa pa (a |> expand_alias |> expa pa) expb pb b

let rec expand_tybody pol = function
  | BParam s -> s
  | BCons b -> StateSet.singleton (mkstate pol (expand_comp pol b) StateSet.empty)
and expand_comp pol t =
  TypeLat.lift (Components.pmap expand_tybody pol t)


let join p x y =
  let tx, ty = expand_both expand_comp p x expand_comp p y in
  TypeLat.(of_list (join_comps p (fun p -> StateSet.union) (as_list tx) (as_list ty)))


let merge s s' =
  assert (s.pol = s'.pol);
  s.cons <- join s.pol s.cons s'.cons;
  s.flow <- StateSet.union s.flow s'.flow;
  check_polarity s

(* FIXME: parsing recursive types needs more testing *)
let rec compile_set ctx r pol = function
| TNamed (v, args) ->
   (match VarMap.mem v r, args with
   | true, [] -> StateSet.singleton (VarMap.find v r)
   | true, _ -> failwith "unexpected args to rectype"
   | false, args ->
      Typector.ty_named ctx v args Location.internal 
      |> compile_cons ctx r pol)
| TCons c -> compile_cons ctx r pol c
| TRec (v, t) ->
   let s = zero pol in
   let ss' = (compile_set ctx (VarMap.add v s r) pol t) in
   assert (not (StateSet.mem ss' s)); (* guardedness check *)
   StateSet.iter ss' (merge s);
   StateSet.singleton s
| TZero p' ->
   if pol <> p' then failwith "zero of wrong polarity"; (* FIXME *)
   StateSet.empty
| TAdd (p', s, t) ->
   if pol <> p' then failwith "wrong add"; (* FIXME *)
   StateSet.union (compile_set ctx r pol s) (compile_set ctx r pol t)
| TWildcard -> failwith "no wildcard allowed here"
and compile_cons ctx r pol c = StateSet.singleton
  { id = fresh_id (); 
    pol; 
    cons = TypeLat.lift (Components.pmap (compile_set ctx r) pol c);
    flow = StateSet.empty }

let compile_type ctx pol t =
  (* FIXME: special-case one-element sets *)
  let s = zero pol in
  StateSet.iter (compile_set ctx VarMap.empty pol t) (merge s);
  s



let rec compile_type_pair ctx r = function
| TWildcard -> flow_pair ()
| TNamed (v, args) ->
   Typector.ty_named ctx v args Location.internal
      |> cons_pair ctx r
| TCons c ->
   cons_pair ctx r c
| TRec (v, t) -> failwith "rec?"
| TZero _ -> failwith "zero not allowed"
| TAdd _ -> failwith "add not allowed"
and cons_pair ctx r c =
  let ct = Components.pmap (fun p t -> compile_type_pair ctx r t) Pos c in
  let pol_swap p (x, y) = match p with Neg -> x | Pos -> y in
  cons Neg (Components.pmap pol_swap Neg ct), cons Pos (Components.pmap pol_swap Pos ct)

let compile_type_pair ctx t = compile_type_pair ctx VarMap.empty t


let print_automaton ctx diagram_name ppf (map : (string -> rawstate -> unit) -> unit) =
  let open Format in
  let names = StateTbl.create 20 in
  map (fun n s -> StateTbl.add names s n);

  let dumped = StateTbl.create 20 in
  let pstate ppf s = fprintf ppf "n%d" s.id in
  let rec dump s =
    let name = try Some (StateTbl.find names s) with Not_found -> None in
    if StateTbl.mem dumped s then () else begin
      StateTbl.add dumped s s;
      let name = (match name with None -> "" | Some n -> n ^ ": ") in
      let ctor = s.cons |> TypeLat.pmap (fun _ _ -> TZero Neg) s.pol |> TypeLat.to_typeterm s.pol in
      fprintf ppf "%a [label=\"%s%a (%d)\"];\n" pstate s name (Printers.pp_typeterm ctx) ctor s.id;
      List.iter (fun (f, ss') -> 
        StateSet.iter ss'
          (fun s' -> 
            fprintf ppf "%a -> %a [label=\"%s\"];\n" pstate s pstate s' f;
            dump s'))
        (TypeLat.list_fields s.cons);
      StateSet.iter s.flow (fun s' -> dump s')
    end in
  fprintf ppf "digraph %s{\n" diagram_name;
  (* dump structural constraints *)
  StateTbl.iter (fun s n -> dump s) names;
  (* dump dataflow constraints *)
  StateTbl.iter (fun s _ ->
    if s.pol = Neg then StateSet.iter s.flow (fun s' -> 
        fprintf ppf "%a -> %a [style=dashed, constraint=false]\n" pstate s pstate s'
      )) dumped;
  fprintf ppf "}\n"




let find_reachable (roots : rawstate list) =
  let states = StateTbl.create 20 in
  let rec search s acc =
    if StateTbl.mem states s then acc else begin
      StateTbl.add states s ();
      s :: List.fold_right (fun (f, ss') acc -> StateSet.fold_left ss' acc
        (fun acc s' -> search s' acc)) (TypeLat.list_fields s.cons) acc
    end in
  List.fold_right search roots []

let garbage_collect (root : rawstate) =
  let states = find_reachable [root] in
  let state_set = List.fold_left StateSet.add StateSet.empty states in
  List.iter (fun s -> s.flow <- StateSet.inter s.flow state_set) states
                
let make_table s f =
  let t = StateTbl.create 20 in
  StateSet.iter s (fun s -> StateTbl.add t s (f s)); 
  t

(* FIXME: deterministic? ID-dependent? *)
let decompile_automaton (roots : rawstate list) : typeterm list =
  let state_list = find_reachable roots in
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
    Symbol.intern (if id < 26 then String.make 1 (Char.chr (Char.code 'A' + id)) else Printf.sprintf "T_%d" (id - 26)) in
  let fresh_var = let var_id = ref (-1) in fun () -> incr var_id; name_var !var_id in
  let state_vars = StateTbl.create 20 in
  List.iter (fun (ss, ss') -> 
    let v = TNamed (fresh_var (), []) in
    let iter ss = StateSet.iter ss (fun s -> StateTbl.add state_vars s v) in
    iter ss; iter ss') biclique_decomposition;


  let state_rec_var = StateTbl.create 20 in
  let rec decompile s =
    if StateTbl.mem state_rec_var s then
      match StateTbl.find state_rec_var s with
      | Some v -> TNamed (v, [])
      | None -> let v = fresh_var () in (StateTbl.replace state_rec_var s (Some v); TNamed (v, []))
    else
      let vars = StateTbl.find_all state_vars s in
      StateTbl.add state_rec_var s None;
      let t = TypeLat.pmap (fun p' ss' -> ty_add p' (List.map decompile (StateSet.to_list ss'))) s.pol s.cons in
      let tv = ty_add s.pol (TypeLat.to_typeterm s.pol t :: vars) in
      let visited = StateTbl.find state_rec_var s in
      StateTbl.remove state_rec_var s;
      match visited with
      | None -> tv
      | Some v -> TRec (v, tv) in
  List.map decompile roots
  

type constraint_state = Proved | Proving
let constrain loc sp_orig sn_orig =
  assert (sp_orig.pol = Pos);
  assert (sn_orig.pol = Neg);
  let seen = Hashtbl.create 20 in
  let rec closure sp sn =
    if Hashtbl.mem seen (sp.id, sn.id) then
      match Hashtbl.find seen (sp.id, sn.id) with
      | Proved -> []
      | Proving -> [Location.empty,Location.empty,Typector.Wrong_arity (42,42)]
    else begin
      Hashtbl.add seen (sp.id, sn.id) Proving;
      StateSet.iter sn.flow (fun s -> merge s sp);
      StateSet.iter sp.flow (fun s -> merge s sn);
      let tp, tn = expand_both expand_comp sp.pol sp.cons expand_comp sn.pol sn.cons in
      sp.cons <- tp; sn.cons <- tn;
      (* lub X <= glb Y, i.e. forall i, j, X[i] <= Y[j] *)
      let cp = TypeLat.as_list tp and cn = TypeLat.as_list tn in
      let r = 
        List.fold_right (fun x rs -> 
          List.fold_right (fun y rs -> 
            Components.lte (pol_flip closure_l) x y @ rs) cn rs) cp [] in
      Hashtbl.replace seen (sp.id, sn.id) Proved;
      r
    end
  and closure_l ssp ssn =
    StateSet.fold_left ssp [] (fun rs sp ->
      rs @ StateSet.fold_left ssn rs (fun rs sn ->
        rs @ closure sp sn)) in
  let as_error (la, lb, reason) =
    Error.Conflict (loc, la, lb, reason) in
  closure sp_orig sn_orig |> List.map as_error





(* Deterministic automata *)


type dstate_id = int

module rec DState : sig
  type dstate = 
    { d_id : dstate_id;
      d_pol : polarity;
      mutable d_cons : dstate TypeLat.t;
      mutable d_flow : DStateSet.t; }
end = struct
  type dstate =
    { d_id : dstate_id;
      d_pol : polarity;
      mutable d_cons : dstate TypeLat.t;
      mutable d_flow : DStateSet.t }
end
and DStateSet : Intmap.S with type elt = DState.dstate = 
  Intmap.Fake (struct type t = DState.dstate let get_id = fun s -> s.DState.d_id end)

open DState

type dstate = DState.dstate
let mkdstate pol cons flow =
  DState.{ d_id = fresh_id ();
           d_pol = pol;
           d_cons = cons;
           d_flow = flow }
let fresh_dstate p =
  mkdstate p TypeLat.join_ident DStateSet.empty

module DStateHash = struct type t = dstate let equal x y = x == y let hash x = x.d_id end
module DStateTbl = Hashtbl.Make (DStateHash)

(* Convert a DFA into an NFA *)
let clone f =
  let states = DStateTbl.create 20 in
  let rec copy_state loc s =
    if DStateTbl.mem states s then
      DStateTbl.find states s 
    else begin
      let s' = { id = fresh_id ();
                 pol = s.d_pol;
                 cons = TypeLat.join_ident;
                 flow = StateSet.empty } in
      DStateTbl.add states s s';
      s'.cons <- TypeLat.pmap (fun pol d ->
        assert (pol = d.d_pol);
        StateSet.singleton (copy_state loc d)) s.d_pol s.d_cons
      |> TypeLat.change_locations loc;
      s'.flow <- DStateSet.fold_left s.d_flow StateSet.empty
        (fun flow d -> StateSet.add flow (copy_state loc d));
      s' 
    end in
  f copy_state




(* Convert an NFA (bunch of states) into a DFA (bunch of dstates) *)
let determinise old_states =
  (* DFA states correspond to sets of NFA states *)
  let module M = Map.Make (StateSet) in
  let dstates = ref M.empty in
  let states_follow p (s : StateSet.t) : StateSet.t TypeLat.t =
    StateSet.fold_left s TypeLat.join_ident (fun c s -> join p c s.cons) in
  let rec follow p s =
    if M.mem s !dstates then
      M.find s !dstates
    else begin
      let d = fresh_dstate p in
      dstates := M.add s d !dstates;
      d.d_cons <- TypeLat.pmap follow p (states_follow p s);
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
    d.d_flow <- StateSet.fold_left ss DStateSet.empty (fun ds s ->
      DStateSet.union ds (flows_to s)));
  let all_dstates = !dstates |> M.bindings |> List.map snd in
  (fun s -> M.find (StateSet.singleton s) !dstates), all_dstates


(* Construct a minimal DFA using (roughly) Hopcroft's algorithm *)
let minimise dstates =
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
      assert (d1.d_pol = d2.d_pol);
      TypeLat.(subs_comps d1.d_pol (fun pol x y -> true) (as_list d1.d_cons) (as_list d2.d_cons)) in
    sub_ctor d d' && sub_ctor d' d in
    

  let initial_partition = [ dstates ]
    |> repartition (fun d d' -> d.d_pol = d'.d_pol)
    |> repartition same_ctor
    |> repartition (fun d d' -> DStateSet.compare d.d_flow d'.d_flow = 0)
    |> List.map DStateSet.of_list in


  let predecessors = DStateTbl.create 20 in
  dstates |> List.iter (fun d ->
    TypeLat.iter (fun p d' -> DStateTbl.add predecessors d' d) d.d_pol d.d_cons);

  (* Find predecessors of a set ds' of dstates *)
  let pred_ctor p ds' =
    let ds = DStateSet.(fold_left ds' empty
      (fun ds d' -> union ds (of_list (DStateTbl.find_all predecessors d')))) in
    DStateSet.fold_left ds [] (fun t d ->
      TypeLat.join_comps p (fun p x y -> DStateSet.union x y) t
        (TypeLat.as_list (TypeLat.pmap (fun p d' -> 
        if DStateSet.mem ds' d' then
          DStateSet.singleton d
        else DStateSet.empty) d.d_pol d.d_cons))) in

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
    (DStateSet.min_elt p).d_pol in

  let rec refine ps =
    check_disjoint DStateSet.empty ps;
    (*
    dump_partition ps;*)
    match !active with
    | [] -> ps
    | (ds :: rest) ->
      active := rest;
      let pol = partition_polarity ds in
      refine (TypeLat.pfold_comps split pol (pred_ctor pol ds) ps) in

  let remap_tbl = DStateTbl.create 20 in
  let new_dstates = initial_partition |> refine |> List.map (fun p ->
    let d = fresh_dstate (partition_polarity p) in
    DStateSet.iter p (fun x -> DStateTbl.add remap_tbl x d);
    (d, DStateSet.to_list p |> List.hd)) in

  let remap d = DStateTbl.find remap_tbl d in
  
  new_dstates |> List.iter (fun (s, d) ->
    s.d_cons <- TypeLat.pmap (fun p x -> remap x) d.d_pol d.d_cons;
    s.d_flow <- DStateSet.fold_left d.d_flow DStateSet.empty (fun flow x -> DStateSet.add flow (remap x)));

  remap


(* Entailment of flow edges on deterministic automata *)


let add_flow dn dp =
  dn.d_flow <- DStateSet.add dn.d_flow dp;
  dp.d_flow <- DStateSet.add dp.d_flow dn

let rec dexpand_tybody pol = function
  | BParam s -> s
  | BCons b -> mkdstate pol (dexpand_comp pol b) DStateSet.empty
and dexpand_comp pol t =
  TypeLat.lift (Components.pmap dexpand_tybody pol t)

let rec entailed dn dp =
  assert (dn.d_pol = Neg && dp.d_pol = Pos);
  assert (DStateSet.mem dn.d_flow dp = DStateSet.mem dp.d_flow dn);
  if DStateSet.mem dn.d_flow dp then true else begin
    add_flow dn dp;
    let tn, tp = expand_both dexpand_comp dn.d_pol dn.d_cons dexpand_comp dp.d_pol dp.d_cons in
    (* glb X <= lub Y, i.e. exists i,j, X[i] <= Y[j] *)
    let cn = TypeLat.as_list tn and cp = TypeLat.as_list tp in
    let b = List.exists (fun x -> 
      List.exists (fun y -> Components.lte' (pol_flip entailed) x y) cp) cn in
    if b then
      true
    else begin
      dn.d_flow <- DStateSet.remove dn.d_flow dp;
      dp.d_flow <- DStateSet.remove dp.d_flow dn;
      false
    end
  end

let subsumed map =
  let seen = StateTbl.create 20 in
  let add sa db =
    let open StateTbl in
    if mem seen sa then begin
      let s = find seen sa in
      if DStateSet.mem s db then
        true
      else begin
        replace seen sa (DStateSet.add s db);
        false
      end
    end else begin
      add seen sa (DStateSet.singleton db);
      false
    end in

  let rec subsume pol sa db =
    assert (pol = db.d_pol && pol = sa.pol);
    (* db is rigid.
       pol = Pos: sa <= db
       pol = Neg: sa >= db *)
    if add sa db then true else begin
      let ta, tb = expand_both expand_comp pol sa.cons dexpand_comp pol db.d_cons in
      TypeLat.(subs_comps pol subsume_all (as_list ta) (as_list tb))
    end
  and subsume_all pol ssa db =
    StateSet.fold_left ssa true (fun r sa -> r && subsume pol sa db) in


  let all_entailed r dns dps =
    DStateSet.fold_left dns r (fun r dn ->
      DStateSet.fold_left dps r (fun r dp ->
        r && entailed dn dp)) in

  let check_dataflow r =
    StateTbl.fold (fun sa dbs r ->
      match sa.pol with
      | Pos -> r
      | Neg ->
         StateSet.fold_left sa.flow r (fun r sa' ->
           let dbs' = try StateTbl.find seen sa' with Not_found -> DStateSet.empty in
           (* dbs <= sa <= sa' <= dbs' *)
           all_entailed r dbs dbs')) seen r in
  
  let r = map subsume in
  check_dataflow r


let find_reachable_dstates (roots : dstate list) =
  let states = DStateTbl.create 20 in
  let rec search s acc =
    if DStateTbl.mem states s then acc else begin
      DStateTbl.add states s ();
      s :: TypeLat.pfold (fun p s acc -> search s acc) s.d_pol s.d_cons acc
    end in
  List.fold_right search roots []

let optimise_flow (roots : dstate list) =
  let states = find_reachable_dstates roots in
  let state_set = DStateSet.of_list states in
  let flows = states
    |> List.rev
    |> List.map (fun sn ->
      match sn.d_pol with
      | Pos -> []
      | Neg -> sn.d_flow
        |> DStateSet.inter state_set
        |> DStateSet.to_list
        |> List.map (fun sp -> (sn, sp)))
    |> List.concat in
  let clear_flows () =
    List.iter (fun s -> s.d_flow <- DStateSet.empty) states in
  (* remove flows and re-add them in reverse postorder *)
  clear_flows ();
  let rec filter_flows = function
    | [] -> []
    | (sn, sp) as flow :: flows ->
       if entailed sn sp then filter_flows flows
       else (add_flow sn sp; flow :: filter_flows flows) in
  let flows' = filter_flows flows in
  clear_flows ();
  flows' |> List.iter (fun (sn, sp) -> add_flow sn sp);
