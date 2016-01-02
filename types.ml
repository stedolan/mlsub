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
    | SyntaxErr of Location.t
    | Unbound of Location.t * Symbol.t
  let print ppf = function
    | (Conflict (la, a, lb, b)) ->
       (Location.LocSet.iter (Location.print ppf) la;
        Location.LocSet.iter (Location.print ppf) lb;
        Format.fprintf ppf "%s - %s\n%!" a b)
    | (SyntaxErr l) ->
       (Format.fprintf ppf "syntax error\n";
        Location.print ppf l)
    | Unbound (l, v) ->
       (Format.fprintf ppf "'%s' not in scope\n" (Symbol.to_string v);
        Location.print ppf l)
  let excuse = Conflict (Location.empty, "?", Location.empty, "?")
end
  
module Components = struct
  type 'a t =
    | Func of (Location.set * 'a) list * (Location.set * 'a) SMap.t * unit SMap.t * (Location.set * 'a)
    | Object of (Location.set * 'a) SMap.t
    | List of Location.set * 'a
    | Base of Location.set * Symbol.t

  let locations = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> Location.join l r) pos 
         (SMap.fold (fun k (l, a) r -> Location.join l r) kwargs l)
    | Object o -> SMap.fold (fun _ (l, _) locs -> Location.join l locs) o Location.empty
    | List (l, _) -> l
    | Base (l, _) -> l

  let change_locations l' = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l', a)) pos, 
             SMap.map (fun (l, a) -> (l', a)) kwargs,
             reqs,
             (l', res))
    | Object o -> Object (SMap.map (fun (l, a) -> (l', a)) o)
    | List (l, a) -> List (l', a)
    | Base (l, s) -> Base (l', s)

  let pmap f pol = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       Func (List.map (fun (l, a) -> (l, f (polneg pol) a)) pos,
             SMap.map (fun (l, a) -> (l, f (polneg pol) a)) kwargs,
             reqs,
             (l, f pol res))
    | Object o -> Object (SMap.map (fun (l, x) -> (l, f pol x)) o)
    | List (l, a) -> List (l, f pol a)
    | Base (l, s) -> Base (l, s)

  let pfold f pol t x = match t with
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.fold_right (fun (l, a) r -> f (polneg pol) a r) pos
         (SMap.fold (fun k (l, a) r -> f (polneg pol) a r) kwargs
            (f pol res x))

    | Object o -> SMap.fold (fun k (l, t) x -> f pol t x) o x
    | List (l, a) -> f pol a x
    | Base (l, s) -> x

  let cmp_component (type a) (type b) (x : a t) (y : b t) = match x, y with
    | Func (pos, _, _, _), Func (pos', _, _, _) -> List.length pos = List.length pos'
    | Object _, Object _ -> true
    | List _, List _ -> true
    | Base (l, s), Base (l', s') -> s = s'
    | _, _ -> false

  let join pol f x y = match x, y, pol with
    | Func (pos, kwargs, reqs, (l, res)), Func (pos', kwargs', reqs', (l', res')), pol ->
       let kw_merge k x y = match pol, x, y with
         | pol, Some (l, a), Some (l', a') -> Some
            (Location.join l l',
             f (polneg pol) a a')

         (* negatively, take union of keyword arguments *)
         | Neg, (Some _ as arg), None
         | Neg, None, (Some _ as arg) -> arg

         (* positively, take intersection of keyword arguments *)
         | Pos, Some _, None
         | Pos, None, Some _ -> None

         | pol, None, None -> None in
       let req_merge k x y = match pol, x, y with
         | _, Some (), Some () -> Some ()
         | _, None, None -> None

         (* negatively, take intersection of required arguments *)
         | Neg, Some (), None
         | Neg, None, Some () -> None

         (* positively, take union of required arguments *)
         | Pos, Some (), None
         | Pos, None, Some () -> Some () in
       Func (List.map2 (fun (l, a) (l', a') -> (Location.join l l', f (polneg pol) a a')) pos pos',
             SMap.merge kw_merge kwargs kwargs',
             SMap.merge req_merge reqs reqs',
             (Location.join l l', f pol res res'))

    | Object x, Object y, Pos ->
       Object (SMap.merge (fun k x y ->
         match x, y with (* lub takes intersection of fields *)
         | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Pos x y)
         | _, _ -> None) x y)
    | Object x, Object y, Neg ->
       Object (SMap.merge (fun k x y ->
         match x, y with (* glb takes union of fields *)
         | Some (lx, x), Some (ly, y) -> Some (Location.join lx ly, f Neg x y)
         | Some a, None
         | None, Some a -> Some a
         | None, None -> None) x y)

    | List (l, a), List (l', a'), pol ->
       List (Location.join l l', f pol a a')

    | Base (l, s), Base (l', s'), pol when s = s' ->
       Base (Location.join l l', s)

    | _, _, _ ->
       assert (cmp_component x y); assert false

  let lte (type a) (type b) f (x : a t) (y : b t) = match x, y with
    | Func (pos, kwargs, reqs, (l, res)), Func (pos', kwargs', reqs', (l', res')) when cmp_component x y ->
       let kw_cmp r =
         SMap.fold (fun k (l', t') r ->
           if SMap.mem k kwargs then
             let (l, t) = SMap.find k kwargs in
             f Neg t t' @ r
           else [Reason.Conflict (locations x, "keyword", l', Symbol.to_string k)] @ r) kwargs' r in
       let req_cmp r =
         SMap.fold (fun k () r ->
           if SMap.mem k reqs' then r else
             [Reason.Conflict (locations x, "required+", locations y, Symbol.to_string k)] @ r) reqs r in
       f Pos res res' |> req_cmp |> kw_cmp |>
           List.fold_right2 (fun (l, x) (l, y) r -> f Neg x y @ r) pos pos'

    | Object ox, Object oy -> 
       SMap.fold (fun k (yl, yk) r -> 
         if SMap.mem k ox then
           let (xl, xk) = SMap.find k ox in
           f Pos xk yk @ r
         else [Reason.Conflict (locations x, "{}", yl, Symbol.to_string k)] @ r) oy []

    | List (l, a), List (l', a') ->
       f Pos a a'

    | Base (l, s), Base (l', s') when s = s' ->
       []

    (* error cases *)
    | x, y ->
       let name = function
       | Func _ -> "function"
       | Object _ -> "object"
       | List _ -> "list"
       | Base (_, s) -> Symbol.to_string s in
       [Reason.Conflict (locations x, name x, locations y, name y)]

  let list_fields = function
    | Func (pos, kwargs, reqs, (l, res)) -> 
       List.mapi (fun i (l, a) -> (string_of_int i, a)) pos @
         (SMap.bindings kwargs |> List.map (fun (k, (l, a)) -> (Symbol.to_string k, a))) @
         ["res", res]
    | Object o -> List.map (fun (k, (_, v)) -> (Symbol.to_string k, v)) (SMap.bindings o)
    | List (l, a) -> ["e", a]
    | Base (l, s) -> []

  let print pr pol ppf = function
    | Func (pos, kwargs, reqs, (l, res)) ->
       let args = List.map (fun (l, a) -> (None, Some a)) pos @
         (SMap.merge (fun k arg req -> match arg, req with
          | Some (l, a), None -> Some (Some (Symbol.to_string k ^ "?"), Some a)
          | Some (l, a), Some () -> Some (Some (Symbol.to_string k), Some a)
          | None, Some () -> Some (Some (Symbol.to_string k), None)
          | None, None -> None) kwargs reqs |> SMap.bindings |> List.map (fun (a, b) -> b)) in
       let pr_arg ppf = function
         | None, None -> ()
         | None, Some t -> Format.fprintf ppf "%a" (pr (polneg pol)) t
         | Some name, Some t -> Format.fprintf ppf "%s : %a" name (pr (polneg pol)) t
         | Some name, None -> Format.fprintf ppf "%s : <err>" name in
       let comma ppf () = Format.fprintf ppf ",@ " in
       Format.fprintf ppf "(%a) -> %a"
         (Format.pp_print_list ~pp_sep:comma pr_arg) args
         (pr pol) res
    | Object _ as o ->
       let rec pfield ppf = function
         | [] -> ()
         | [f, x] ->
            Format.fprintf ppf "%s :@ %a" f (pr pol) x
         | (f, x) :: xs ->
            Format.fprintf ppf "%s :@ %a,@ %a" f (pr pol) x pfield xs in
       Format.fprintf ppf "{%a}" pfield (list_fields o)
    | List (l, a) ->
       Format.fprintf ppf "List[%a]" (pr pol) a
    | Base (l, s) ->
       Format.fprintf ppf "%s" (Symbol.to_string s)
end

module type TYPES = sig
    type 'a t
    val lift : 'a Components.t -> 'a t
    val join : polarity -> (polarity -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    val join_ident : 'a t

    val lte_pn : ('a -> 'a -> Reason.t list) -> 'a t -> 'a t -> Reason.t list
    val lte_np : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val subs : polarity -> (polarity -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

    val pmap : (polarity -> 'a -> 'b) -> polarity -> 'a t -> 'b t
    val pfold : (polarity -> 'a -> 'r -> 'r) -> polarity -> 'a t -> 'r -> 'r
    val iter : (polarity -> 'a -> unit) -> polarity -> 'a t -> unit

    val print : (polarity -> 'a printer) -> polarity -> 'a t printer
    val list_fields : 'a t -> (string * 'a) list

    val change_locations : Location.set -> 'a t -> 'a t
  end

module TypeLat : TYPES = struct
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
      Components.lte (fun p x y -> if pol_flip f p x y then [] else [Reason.excuse]) x y = [])  xs) ys

  let rec subs pol f xs ys =
    (* lub X <= lub Y or glb X >= glb Y *)
    match xs with
    | [] -> true
    | x :: xs -> match List.partition (Components.cmp_component x) ys with
      | [], ys -> false
      | [y], ys ->
         (match pol with
         | Pos -> Components.lte (fun p x y -> if f p x y then [] else [Reason.excuse]) x y = []
         | Neg -> Components.lte (fun p y x -> if f (polneg p) x y then [] else [Reason.excuse]) y x = [])
         && subs pol f xs ys
      | y1 :: y2 :: _, _ -> failwith "two terms in same component"

  let list_fields x =
    x |> List.map Components.list_fields |> List.concat

  let print pr pol ppf = function
    | [] -> Format.fprintf ppf "%s" (match pol with Pos -> "Bot" | Neg -> "Top")
    | ty ->
       let pp_sep ppf () = Format.fprintf ppf "@ %s@ " (match pol with Pos -> "|" | Neg -> "&") in
       Format.pp_print_list ~pp_sep (Components.print pr pol) ppf ty

  let change_locations l = List.map (Components.change_locations l)
end

let cons_name pol = print_to_string (TypeLat.print (fun pol ppf x -> ()) pol)


type var = string

type 'a typeterm = 
| TVar of 'a
| TCons of ('a typeterm) TypeLat.t
| TAdd of 'a typeterm * 'a typeterm
| TRec of 'a * 'a typeterm


let ty_add t t' loc = TAdd (t loc, t' loc)
let ty_var v loc = TVar v
let ty_list e loc = TCons (TypeLat.lift (Components.List (Location.one loc, e loc)))
let ty_fun pos kwargs res loc = TCons (TypeLat.lift (Components.Func (
  List.map (fun a -> (Location.one loc, a loc)) pos,
  SMap.map (fun (a, req) -> (Location.one loc, a loc)) kwargs,
  SMap.filter (fun k (a, req) -> req) kwargs |> SMap.map (fun _ -> ()),
  (Location.one loc, res loc))))
let ty_zero loc = TCons (TypeLat.join_ident)
let ty_obj o loc = TCons (TypeLat.lift (Components.Object (SMap.map (fun x -> (Location.one loc, x loc)) o)))
let ty_base s loc = TCons (TypeLat.lift (Components.Base (Location.one loc, s)))
                       
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
     fprintf ppf "@[%a@]" (TypeLat.print (gen_print_typeterm vstr) pol) cons
  | TAdd (t1, t2) -> 
    let op = match pol with Pos -> "|" | Neg -> "&" in
    fprintf ppf "@[%a %s@ %a@]" (gen_print_typeterm vstr pol) t1 op (gen_print_typeterm vstr pol) t2
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
let decompile_automaton (roots : state list) : var typeterm list =
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
    if id < 26 then String.make 1 (Char.chr (Char.code 'A' + id)) else Printf.sprintf "T_%d" (id - 26) in
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
  List.map decompile roots
  


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
    (List.hd (DStateSet.to_list p)).d_pol in

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


let rec entailed dn dp =
  assert (dn.d_pol = Neg && dp.d_pol = Pos);
  assert (DStateSet.mem dn.d_flow dp = DStateSet.mem dp.d_flow dn);
  if DStateSet.mem dn.d_flow dp then true else begin
    dn.d_flow <- DStateSet.add dn.d_flow dp;
    dp.d_flow <- DStateSet.add dp.d_flow dn;
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


let optimise_flow (roots : state list) = ()
(*
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
*)

