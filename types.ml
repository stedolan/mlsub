open Typector
open Variance
open Exp

(* Typing contexts *)

type tybody =
| BParam of Symbol.t
| BCons of tybody Typector.Components.t

type typedef =
| TAlias of variance SMap.t * tybody
| TOpaque of variance SMap.t


type context = typedef SMap.t

let empty_context = SMap.empty

let add_to_context err ctx name ty =
  if SMap.mem name ctx then
    failwith "reused name"
  else
    SMap.add name ty ctx


let add_type_alias err name param_list term ctx =
  let rec mk_params s = function
    | [] -> s
    | TParam (v, p) :: ps ->
       mk_params (if SMap.mem p s then failwith "duplicate param" else SMap.add p v s) ps in
  let params = mk_params SMap.empty param_list in
  let rec inferred_variances = ref (SMap.map (fun _ -> VNone) params) in
  let use param pol =
    inferred_variances := 
      SMap.add param (vjoin 
        (SMap.find param !inferred_variances)
        (variance_of_pol pol)) !inferred_variances in

  let rec check pol = function
    | TNamed (t, args) when SMap.mem t params ->
       (match args with [] -> (use t pol; BParam t) | _ -> failwith "nope")
    | TNamed (t, args) ->
       (match SMap.find t ctx with
       | TOpaque params ->
          BCons (ty_base t Location.internal)
       | _ -> failwith "unimplemented named type")
    | TCons cons -> BCons (Typector.Components.pmap check pol cons) 
    | TZero _ -> failwith "nzero"
    | TAdd _ -> failwith "nadd"
    | TRec _ -> failwith "nrec" in

  let param_variances = SMap.merge (fun p asc infer -> match asc, infer with
    | None, _ | _, None -> assert false (* maps have same keys *)
    | Some (Some asc), Some infer -> assert (vlte infer asc); Some asc
    | Some None, Some infer -> Some infer) params !inferred_variances in

  add_to_context err ctx name (TAlias (param_variances, check Pos term))

let add_opaque_type err name param_list ctx =
  let rec check_params s = function
    | [] -> s
    | TParam (v, p) :: ps ->
       if SMap.mem p s then (failwith "duplicate param"; check_params s ps) else
         let s' = match v with Some v -> SMap.add p v s | None -> failwith "variance required"; s in
         check_params s' ps in
  add_to_context err ctx name (TOpaque (check_params SMap.empty param_list))



(* Debugging *)

let print_to_string (pr : 'a printer) (x : 'a) : string =
  let buf = Buffer.create 100 in
  let ppf = Format.formatter_of_buffer buf in
  Format.fprintf ppf "%a%!" pr x;
  Buffer.contents buf


let string_of_var v = Symbol.to_string v

open Format

let printp paren ppf fmt =
  let openbox ppf = if paren then fprintf ppf "@[(" else fprintf ppf "@[" in
  let closebox ppf = if paren then fprintf ppf "@])" else fprintf ppf "@]" in
  openbox ppf;
  kfprintf closebox ppf fmt


let rec print_typeterm ppf = function
  | TZero Pos -> fprintf ppf "nothing"
  | TZero Neg -> fprintf ppf "any"
  | TNamed (v, []) -> fprintf ppf "%s" (string_of_var v)
  | TNamed (v, args) -> 
     let print_arg ppf = function
       | APos t -> fprintf ppf "+%a" print_typeterm t
       | ANeg t -> fprintf ppf "-%a" print_typeterm t
       | AUnspec t -> fprintf ppf "%a" print_typeterm t
       | ANegPos (s, t) -> fprintf ppf "-%a +%a" print_typeterm s print_typeterm t in
     let comma ppf () = Format.fprintf ppf ",@ " in
     fprintf ppf "%s[%a]" (string_of_var v) (Format.pp_print_list ~pp_sep:comma print_arg) args
  | TCons cons ->
     fprintf ppf "@[%a@]" (Components.print (fun pol -> print_typeterm) Pos) cons
  | TAdd (p, t1, t2) -> 
    let op = match p with Pos -> "|" | Neg -> "&" in
    fprintf ppf "@[%a %s@ %a@]" print_typeterm t1 op print_typeterm t2
  | TRec (v, t) ->
    fprintf ppf "rec %s = %a" (string_of_var v) print_typeterm t


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
  type 'a t = 'a Components.t list
  let lift t = [t]
  let pmap f pol ty = List.map (Components.pmap f pol) ty
  let rec pfold f pol ty x = match ty with
    | [] -> x
    | t :: ts -> Components.pfold f pol t (pfold f pol ts x)

  let iter f p x = pfold (fun pol x r -> f pol x) p x ()

  let rec join pol f xs ys = match xs with
    | [] -> ys
    | x :: xs ->
       match List.partition (Components.cmp_component x) ys with
       | [], ys -> x :: join pol f xs ys
       | [y], ys -> Components.join pol f x y :: join pol f xs ys
       | y1 :: y2 :: _, _ -> failwith "two terms in same component"

  let join_ident = []

  let lte_pn f xs ys =
    (* lub X <= glb Y *)
    (* i.e. forall i,j, Xi <= Yj *)
    List.fold_right (fun x rs -> 
      List.fold_right (fun y rs -> 
        Components.lte (pol_flip f) x y @ rs) ys rs) xs []

  let lte_np f xs ys =
    (* glb X <= lub Y *)
    (* i.e. exists i,j, Xi <= Yj *)
    List.exists (fun x -> List.exists (fun y ->
      Components.lte (fun p x y -> if pol_flip f p x y then [] else [Error.excuse]) x y = []) ys) xs

  let rec subs pol f xs ys =
    (* lub X <= lub Y or glb X >= glb Y *)
    match xs with
    | [] -> true
    | x :: xs -> match List.partition (Components.cmp_component x) ys with
      | [], ys -> false
      | [y], ys ->
         (match pol with
         | Pos -> Components.lte (fun p x y -> if f p x y then [] else [Error.excuse]) x y = []
         | Neg -> Components.lte (fun p y x -> if f (polneg p) x y then [] else [Error.excuse]) y x = [])
         && subs pol f xs ys
      | y1 :: y2 :: _, _ -> failwith "two terms in same component"

  let list_fields x =
    x |> List.map Components.list_fields |> List.concat

  let to_typeterm pol x =
    ty_add pol (List.map (fun t -> TCons t) x)

  let print pr pol ppf = function
    | [] -> Format.fprintf ppf "%s" (match pol with Pos -> "Bot" | Neg -> "Top")
    | ty ->
       let pp_sep ppf () = Format.fprintf ppf "@ %s@ " (match pol with Pos -> "|" | Neg -> "&") in
       Format.pp_print_list ~pp_sep (Components.print pr pol) ppf ty

  let change_locations l = List.map (Components.change_locations l)
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

type pos = PosBrand and neg = NegBrand
type rawstate = State.state


module StateHash = struct type t = State.state let equal x y = x == y let hash x = x.id end
module StateTbl = Hashtbl.Make (StateHash)


module VarOrd = struct type t = tyvar let compare = compare end
module VarMap = Map.Make (VarOrd)

let check_polarity s =
  StateSet.iter s.flow (fun s' -> assert (s'.pol <> s.pol));
  TypeLat.iter (fun p ss -> StateSet.iter ss (fun s -> assert (p = s.pol))) s.pol s.cons

let merge s s' =
  assert (s.pol = s'.pol);
  s.cons <- TypeLat.join s.pol (fun p -> StateSet.union) s.cons s'.cons;
  s.flow <- StateSet.union s.flow s'.flow;
  check_polarity s


let fresh_id_counter = ref 0
let fresh_id () =
  let n = !fresh_id_counter in incr fresh_id_counter; n

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
  { id = fresh_id (); pol = p; cons = TypeLat.join_ident; flow = StateSet.empty }


(* FIXME: Does not detect negative recursion *)
let compile_type (ctx : context) (pol : polarity) (t : typeterm) : rawstate =
  let states = ref [] in
  let epsilon_trans = StateTbl.create 20 in
  let rec compile r p = function
    | TZero p' ->
       (* FIXME *) assert (p = p');
       zero p
    | TNamed (v, []) -> 
      (try VarMap.find v r
       with Not_found ->
         (match SMap.find v ctx with
         | TAlias (params, body) -> failwith "unsupported type alias"
         | TOpaque params -> cons p (Typector.ty_base v Location.internal (* FIXME loc *))
         | exception Not_found -> failwith ("unknown type " ^ Symbol.to_string v)))
    | TNamed (v, args) -> failwith "unsupported parameterised type"
    | TCons c -> cons p (Components.pmap (compile r) p c)
    | TAdd (p', t1, t2) ->
      (* FIXME *) assert (p = p');
      let s1, s2 = compile r p t1, compile r p t2 in
      let s = zero p in
      StateTbl.add epsilon_trans s s1;
      StateTbl.add epsilon_trans s s2;
      states := s :: !states;
      s
    | TRec (v, t) ->
      let s = zero p in
      let s' = compile (VarMap.add v s r) p t in
      StateTbl.add epsilon_trans s s';
      states := s :: !states;
      s in
  let root = compile VarMap.empty pol t in

  (* Remove epsilon transitions *)
  let rec epsilon_closure set s =
    if StateSet.mem set s then set
    else List.fold_left epsilon_closure (StateSet.add set s) (StateTbl.find_all epsilon_trans s) in
  !states |> List.iter (fun s -> StateSet.iter (epsilon_closure StateSet.empty s) (merge s));
  root


let cons_name pol = print_to_string (TypeLat.print (fun pol ppf x -> ()) pol)

let print_automaton diagram_name ppf (map : (string -> rawstate -> unit) -> unit) =
  let names = StateTbl.create 20 in
  map (fun n s -> StateTbl.add names s n);

  let dumped = StateTbl.create 20 in
  let pstate ppf s = fprintf ppf "n%d" s.id in
  let rec dump s =
    let name = try Some (StateTbl.find names s) with Not_found -> None in
    if StateTbl.mem dumped s then () else begin
      StateTbl.add dumped s s;
      let name = (match name with None -> "" | Some n -> n ^ ": ") ^ cons_name s.pol s.cons in
      fprintf ppf "%a [label=\"%s (%d)\"];\n" pstate s name s.id;
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
  

let constrain sp_orig sn_orig =
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
let fresh_dstate p =
  DState.{ d_id = fresh_id ();
           d_pol = p;
           d_cons = TypeLat.join_ident;
           d_flow = DStateSet.empty } 

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
    StateSet.fold_left s TypeLat.join_ident (fun c s -> 
      TypeLat.join p (fun p a b -> StateSet.union a b) c s.cons) in
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
      TypeLat.subs d1.d_pol (fun pol x y -> true) d1.d_cons d2.d_cons in
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
    DStateSet.fold_left ds TypeLat.join_ident (fun t d ->
      TypeLat.join p (fun p x y -> DStateSet.union x y) t
        (TypeLat.pmap (fun p d' -> 
        if DStateSet.mem ds' d' then
          DStateSet.singleton d
        else DStateSet.empty) d.d_pol d.d_cons)) in

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
      refine (TypeLat.pfold split pol (pred_ctor pol ds) ps) in

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


let rec entailed dn dp =
  assert (dn.d_pol = Neg && dp.d_pol = Pos);
  assert (DStateSet.mem dn.d_flow dp = DStateSet.mem dp.d_flow dn);
  if DStateSet.mem dn.d_flow dp then true else begin
    add_flow dn dp;
    if TypeLat.lte_np entailed dn.d_cons dp.d_cons then
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
    if add sa db then true else TypeLat.subs pol subsume_all sa.cons db.d_cons 
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
