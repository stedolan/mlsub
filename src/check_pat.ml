open Exp
open Typedefs
open Tuple_fields
open Util

type action = {
  rhs: exp;
  id: int;
  bound: (ptyp ref * IR.value IR.Binder.t) SymMap.t;
  mutable used: bool;
}

type bindings = ptyp SymMap.t

type 'w pat_row = ('w, pat) Clist.t * (bindings * action)

type 'w pat_matrix = 'w pat_row list

open Peano_nat_types
type 'n dectree =
  { tree: 'n dectree';
    tag: 'n Type_id.tag;
    empty: bool;
    total: bool;
    mutable refcount : int }

and _ dectree' =
  | Done : action -> z dectree'
  | Failure : z dectree'
  | Any : 'n dectree -> 'n s dectree'
  (* Cases: nonempty and sorted *)
  | Cases : (Typedefs.Cons.tuple_tag * 'n fields_split) list -> 'n s dectree'
  | Fields : 'n fields_split -> 'n s dectree'

and 'n fields_split =
  | Proj : ('m, 'n, Tuple_fields.field_name) Clist.prefix * Tuple_fields.fields_open * 'm dectree -> 'n fields_split

module DectreeHash = struct
  let equal_dectree (type a) (type b) (a : a dectree) (b : b dectree) : (a, b) Type_id.eq_result =
    let eq = Type_id.equal a.tag b.tag in
    (match eq with
     | Equal -> assert (a == b)
     | Not_equal -> assert (Obj.repr a != Obj.repr b));
    eq

  let equal_fields_split (type a) (type b) (a : a fields_split) (b : b fields_split) :
        (a, b) Type_id.eq_result =
    let Proj (pfxa, ao, a) = a in
    let Proj (pfxb, bo, b) = b in
    if ao <> bo then Not_equal
    else match equal_dectree a b with
    | Equal ->
       begin match Clist.equal (Stdlib.(=)) pfxa pfxb with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | Not_equal ->
       Not_equal

  let equal_dectree' (type a) (type b) (a : a dectree') (b : b dectree') : (a, b) Type_id.eq_result =
    match a, b with
    | Done a, Done b ->
       assert ((a.id = b.id) = (a == b));
       if a.id = b.id then Equal else Not_equal
    | Failure, Failure ->
       Equal
    | Any a, Any b ->
       begin match equal_dectree a b with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | Cases a, Cases b ->
       let eq_case (sa, ca) (sb, cb) =
         if String.equal sa sb
         then equal_fields_split ca cb
         else Type_id.Not_equal
       in
       if List.compare_lengths a b <> 0 then Not_equal
       else begin match
         List.fold_left
           (Type_id.and_eq)
           (eq_case (List.hd a) (List.hd b))
           (List.map2 eq_case (List.tl a) (List.tl b))
       with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | Fields a, Fields b ->
       begin match
         equal_fields_split a b
       with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | (Done _ | Failure | Any _ | Cases _ | Fields _), _ -> Not_equal

  let mix h =
    let h = h * 0x43297583 in
    let h = h lxor (h lsr 16) in
    let h = h * 0x85ebca6b in
    let h = h lxor (h lsr 13) in
    let h = h * 0xc2b2ae35 in
    let h = h lxor (h lsr 16) in
    h

  let hash_dectree' a =
    mix (Type_id.hash a.tag)

  let hash_fields (Proj (pfx, o, t)) =
    List.fold_left
      (fun h fn -> h + Hashtbl.hash fn)
      (mix (hash_dectree' t) + Hashtbl.hash o)
      (Clist.to_list pfx)

  let hash (type w) (a : w dectree') =
    mix @@ match a with
    | Done a ->
       mix 1 + a.id
    | Failure ->
       mix 2
    | Any a ->
       mix 3 + hash_dectree' a
    | Cases cases ->
       List.fold_left (fun h (s, fs) ->
         h + Hashtbl.hash s + hash_fields fs) (mix 4) cases
    | Fields fs ->
       mix 5 + hash_fields fs
end

module Hashcons = struct
  module Tbl = HashtblT (struct
    type 'w key = 'w dectree'
    type 'w value = 'w dectree
    let hash = DectreeHash.hash
    let equal a b = DectreeHash.equal_dectree' a b
  end)
  type t = Tbl.t
  let fresh_table () : t = Tbl.create 20

  let is_empty (type a) : a dectree' -> bool = function
    | Done _ -> false
    | Failure -> true
    | Any t -> t.empty
    | Cases cases -> List.for_all (fun (_, Proj (_, _, fs)) -> fs.empty) cases
    | Fields (Proj (_, _, fs)) -> fs.empty

  let is_total (type a) : a dectree' -> bool = function
    | Done _ -> true
    | Failure -> false
    | Any t -> t.total
    | Cases cases -> List.for_all (fun (_, Proj (_, _, fs)) -> fs.total) cases
    | Fields (Proj (_, _, fs)) -> fs.total

  let mk tbl (type n) (t : n dectree') : n dectree =
    match Tbl.find tbl t with
    | res ->
       res.refcount <- res.refcount + 1; res
    | exception Not_found ->
       let res =
         { tree = t;
           tag = Type_id.fresh ();
           empty = is_empty t;
           total = is_total t;
           refcount = 1 }
       in
       Tbl.add tbl t res;
       res
end


type pat_head =
  | Hany
  | Hcase of Cons.tuple_tag * pat tuple_fields
  | Hfields of pat tuple_fields

type 'w peeled_row =
  { head: pat_head;
    head_loc: Location.t;
    var: symbol option;
    rest: 'w pat_row }

let rec peel_pat_heads :
  type w . w s pat_matrix -> w peeled_row list
  = function
  | [] -> []
  | (((None,loc) :: _ps), _act) :: _rest ->
     Error.fail loc Syntax
  | (((Some p,head_loc) :: ps), act) :: rest ->
     match p with
     | Pparens p ->
        peel_pat_heads (((p :: ps), act) :: rest)
     | Por (p, q) ->
        peel_pat_heads (((p :: ps), act) :: ((q :: ps), act) :: rest)
     | Pany ->
        {head=Hany; head_loc; var=None; rest=(ps, act)} ::
        peel_pat_heads rest
     | Pvar (v,_) ->
        {head=Hany; head_loc; var=Some v; rest = (ps, act)} ::
        peel_pat_heads rest
     | Ptuple (None, fields) ->
        {head=Hfields fields; head_loc; var=None; rest= (ps, act)} ::
        peel_pat_heads rest
     | Ptuple (Some (tag, _), fields) ->
        {head=Hcase (tag, fields); head_loc; var=None; rest= (ps, act)} ::
        peel_pat_heads rest

type split_kind =
  | Sany
  | Scases of ptyp tuple_fields SymMap.t
  | Sfields of ptyp tuple_fields

let join_pat_conses cons_locs =
  let rec aux = function
    | [] -> assert false
    | [cons, _loc] ->
       Cons.map_one ~neg:(fun _ -> ()) ~pos:(fun _ -> ()) cons
    | (cons, loc) :: rest ->
       let cons' = aux rest in
       if not (Cons.compatible cons cons') then begin
         let loc' =
           List.find_map (fun (cons', loc') -> if Cons.compatible cons cons' then None else Some loc') rest
           |> Option.value ~default:Location.noloc in
         Error.fail loc (Incompatible_patterns loc')
       end;
       let cons = Cons.join_head_one cons cons' in
       Cons.map_one ~neg:(fun _ -> ()) ~pos:(fun _ -> ()) cons
  in
  aux cons_locs

(* Decide the split kind that we are going to check the patterns with. *)
let decide_split_kind ~matchloc env (ty : ptyp) (heads : _ peeled_row list) =
  if List.for_all (function {head=Hany;_} -> true | _ -> false) heads then
    (* If there are no destructuring patterns, any type will do *)
    Sany
  else if List.for_all (function {head=Hany | Hfields _;_} -> true | {head=Hcase _;_} -> false) heads then
    (* All product field constructors *)
    let fields =
      List.concat_map (fun {head; head_loc; _} ->
        match head with
        | Hany -> []
        | Hcase _ -> assert false
        | Hfields fs -> [Cons.Record(None, fs), head_loc])
        heads
      |> join_pat_conses
    in
    match
      Types.match_typ env ty (Location.noloc (*FIXME*)) fields
    with
    | Ok (Record (_, fs)) -> Sfields (map_fields (fun _fn ((),ty) -> ty) fs)
    | Ok _ -> assert false
    | Error e -> Error.fail matchloc (Conflict (`Pat, e))
  else match ty with
  | Tcons {conses;_}
       when List.for_all (function Cons.Record (Some _, _) -> true | _ -> false) conses ->
     let cases =
       conses
       |> List.map (function
         | Cons.Record (Some tag, fields) -> tag, fields
         | _ -> assert false)
       |> List.to_seq
       |> SymMap.of_seq
     in
     Scases cases
  | _ ->
     let inferred_cases =
       List.fold_left (fun acc row ->
         match row.head with
         | Hany | Hfields _ ->
            Error.fail row.head_loc (Illformed_pat `Unknown_cases)
         | Hcase (tag, fields) ->
            let cons = Cons.Record(Some tag, fields) in
            let prev =
              try SymMap.find tag acc
              with Not_found -> []
            in
            SymMap.add tag ((cons,row.head_loc) :: prev) acc)
         SymMap.empty
         heads
       |> SymMap.map join_pat_conses
     in
     let loc = List.concat_map (fun row -> row.head_loc) heads in
     let inferred_cases =
       SymMap.map (Cons.map_one ~neg:(fun _ -> assert false) ~pos:(fun () -> ref (Tcons Cons.bottom))) inferred_cases in
     let cons =
       Cons.make' ~loc (SymMap.fold (fun _tag fields acc -> fields :: acc) inferred_cases [])
     in
     begin match Types.match_typ2 env ty cons with
     | Ok () -> ()
     | Error e -> Error.fail matchloc (Conflict (`Pat, e))
     end;
     Scases (SymMap.map (function
                 | Cons.Record (_, fs) -> map_fields (fun _fn r -> !r) fs
                 | _ -> assert false) inferred_cases)

let any : pat = (Some Pany, noloc)
let pat_or p q : pat = (Some (Por (p, q)), noloc)

(* FIXME as patterns here *)
let read_fields :
  type n m . tag:string option -> (m, n, field_name) Clist.prefix -> n peeled_row -> m pat_row =
  fun ~tag fields {head; head_loc=_; var=_; rest=(row, act)} ->
  match head with
  | Hany ->
     Clist.append (Clist.map (fun _ -> any) fields) row, act
  | Hcase (_, fs)
  | Hfields fs ->
     begin match head, tag with
     | Hcase (tag', _), Some tag -> assert (String.equal tag tag')
     | Hcase (_, _), None -> assert false
     | _ -> ()
     end;
     let lookup fn =
       match get_field_opt fs fn with
       | Some pat -> pat
       | None when fs.fopen = `Open -> any
       | None -> failwith "missing!"
     in
     Clist.append (Clist.map lookup fields) row, act

let matches_tag tag row =
  match row.head with
  | Hany -> true
  | Hfields _ -> true
  | Hcase (tag', _) -> String.equal tag tag'

let row_tail typ row =
  match row.var, row.rest with
  | None, rest -> rest
  | Some v, (pats, (bindings, act)) ->
     (pats, (SymMap.add v typ bindings, act))


let rec split_cases :
  type w . table:_ -> matchloc:_ -> _ -> _ -> (w, ptyp) Clist.t -> w pat_matrix -> w dectree =
  fun ~table ~matchloc env vars typs mat ->
  match typs with
  | [] ->
     begin match mat with
     | [] ->
        Hashcons.mk table Failure
     | ([], (bindings, act)) :: _ ->
        act.used <- true;
        bindings |> SymMap.iter (fun v typ ->
          let (r, _) = SymMap.find v act.bound in
          r := Types.join_ptyp env !r typ);
        Hashcons.mk table (Done act)
     end

  | typ :: typs ->
     let split_fields ~tag fs mat =
        let fopen = fs.fopen in
        let Ex fs = Clist.of_list (list_fields fs) in
        let field_names = Clist.map fst fs in
        let field_types = Clist.map snd fs in
        let mat = List.map (read_fields ~tag field_names) mat in
        let rest =
          split_cases ~table ~matchloc env vars (Clist.append field_types typs) mat in
        Proj (field_names, fopen, rest)
     in

     let mat = peel_pat_heads mat in
       
     match decide_split_kind ~matchloc env typ mat with
     | Sany ->
        let rest = split_cases ~table ~matchloc env vars typs (List.map (row_tail typ) mat) in
        Hashcons.mk table (Any rest)
     | Sfields fs ->
        let fs = split_fields ~tag:None fs mat in
        Hashcons.mk table (Fields fs)
     | Scases cases ->
        let cases = SymMap.mapi (fun tag fs ->
          let mat = List.filter (matches_tag tag) mat in
          split_fields ~tag:(Some tag) fs mat) cases in
        let cases = SymMap.to_seq cases |> List.of_seq in
        Hashcons.mk table (Cases cases)

let find_map_unique ~equal f xs =
  let rec aux u = function
    | [] -> Some u
    | x :: xs ->
       begin match f x with
       | Some u' when equal u u' -> aux u xs
       | _ -> None
       end
  in
  match xs with
  | [] ->
     invalid_arg "find_map_unique: empty list"
  | x :: xs ->
     match f x with
     | None -> None
     | Some u -> aux u xs

module Dectree_tails_K = struct
  type 'k key = Packed : 'n dectree * ('n, 'k, unit) Clist.prefix -> 'k key
  type 'k value = 'k dectree option
  let equal (type k1) (type k2) (Packed (t1, p1) : k1 key) (Packed (t2, p2) : k2 key) : (k1, k2) Type_id.eq_result =
    match DectreeHash.equal_dectree t1 t2 with
    | Not_equal -> Not_equal
    | Equal ->
       match Clist.compare_lengths' p1 p2 with
       | Not_equal -> Not_equal
       | Equal -> Equal

  let hash (Packed (t, p)) =
    DectreeHash.hash_dectree' t + Clist.length p * 84930283
end
module Memo_dectree_tails = HashtblT (Dectree_tails_K)

let rec dectree_tails : type n k a. table:Memo_dectree_tails.t -> (n, k, unit) Clist.prefix -> n dectree -> k dectree option =
  fun ~table pfx t ->
  Memo_dectree_tails.find_or_insert table (Packed (t, pfx)) @@ fun () ->
  let unique_dt f xs =
    find_map_unique ~equal:(fun a b -> DectreeHash.equal_dectree a b |> Type_id.to_bool) f xs in

  match pfx, t.tree with
  | [], _ -> Some t
  | _ :: pfx, Any tail ->
     dectree_tails ~table pfx tail
  | _ :: pfx, Cases cases ->
     cases |> unique_dt (fun (_, Proj (fs, _, t)) ->
       dectree_tails ~table (Clist.append (Clist.map ignore fs) pfx) t)
  | _ :: pfx, Fields (Proj (fs, _, t)) ->
     dectree_tails ~table (Clist.append (Clist.map ignore fs) pfx) t


let counterexamples depth t =
  let tail_tbl = Memo_dectree_tails.create 20 in
  let dectree_tails pfx t = dectree_tails ~table:tail_tbl pfx t in
  let unmatched_fields :
    type n m k . tag:string option -> fopen:Tuple_fields.fields_open ->
      (m, n, field_name) Clist.prefix -> (n, k, _) Clist.prefix ->
      (m, k, pat) Clist.prefix -> (n s, k, pat) Clist.prefix =
    fun ~tag ~fopen fields pfx unmatched ->
    let fs, rest = Clist.split fields pfx unmatched in
    let fields =
      Clist.zip fields fs
      |> Clist.to_list
      |> Tuple_fields.fields_of_list ~fopen
    in
    let pat =
      Ptuple (Option.map (fun s -> s, Location.noloc) tag, fields)
    in
    (Some pat, Location.noloc) :: rest
  in
  
  let rec examples :
    type n k . (n, k, _) Clist.prefix -> n dectree -> (n, k, pat) Clist.prefix list =
    fun pfx dt ->
    if dt.total then []
    else match pfx with
    | [] -> [ [] ]
    | _ :: pfx ->
       match dectree_tails [()] dt with
       | Some tail ->
          (* head must be total! *)
          let ex = examples pfx tail in
          List.map (fun ps -> Clist.(any :: ps)) ex
       | None ->
          match dt.tree with
          | Any _ -> assert false (* has tail *)
          | Fields (Proj (names, fopen, t')) ->
             let ex = examples (Clist.append (Clist.map ignore names) pfx) t' in
             List.map (unmatched_fields ~tag:None ~fopen names pfx) ex
          | Cases cases ->
             let cases =
               cases |> List.map (fun (c, (Proj (names, _, t) as fs)) ->
                 c, fs, dectree_tails (Clist.map ignore names) t)
             in
             let rec group_cases = function
               | [] -> []
               | (tag, Proj (names, fopen, t), None) :: rest ->
                  let ex = examples (Clist.append (Clist.map ignore names) pfx) t in
                  List.map (unmatched_fields ~tag:(Some tag) ~fopen names pfx) ex
                  @ group_cases rest
               | (_, Proj (_, _, _), Some tail) as first :: rest ->
                  let same_tail, rest =
                    List.partition (function
                      | (_, _, Some tail') when Type_id.to_bool (DectreeHash.equal_dectree tail tail') ->
                         true
                      | _ -> false) rest
                  in
                  let ex_tail = examples pfx tail in
                  let pats =
                    (first :: same_tail)
                    |> List.map (fun (tag, (Proj (names, fopen, _)), _) ->
                       let names = Clist.to_list names |> List.map (fun f -> f, any) in
                       let fs = Tuple_fields.fields_of_list names ~fopen in
                       let pat = Ptuple (Some (tag, Location.noloc), fs) in
                       (Some pat, Location.noloc))
                  in
                  let pat = List.fold_left pat_or (List.hd pats) (List.tl pats) in
                  List.map (fun ps -> Clist.(pat :: ps)) ex_tail
                  @ group_cases rest
             in
             group_cases cases
  in
  examples depth t


(*
 * Parse a list of cases into a pattern matrix
 *)

let check_equ_fvs loc p q =
  SymMap.merge (fun k l r ->
   match l, r with
   | None, None -> None
   | Some _ as x, Some _ -> x
   | None, Some _
   | Some _, None ->
      Error.fail loc (Illformed_pat (`Orpat_different_names k)))
  p q

let rec check_fvs_list ps =
  let acc_pat acc p =
    let fvs = check_fvs p in
    SymMap.merge (fun k l r ->
      match l, r with
      | None, None -> None
      | (Some _ as x), None
      | None, (Some _ as x) -> x
      | Some aloc, Some bloc ->
         Error.fail bloc (Illformed_pat (`Duplicate_name (k,aloc))))
      acc fvs
  in
  List.fold_left acc_pat SymMap.empty ps
and check_fvs = function
  | None, _ -> SymMap.empty
  | Some p, loc -> check_fvs' loc p
and check_fvs' ploc = function
  | Pany ->
     SymMap.empty
  | Pvar (v, _) ->
     SymMap.singleton v ploc
  | Ptuple (_, fs) ->
     check_fvs_list (List.map snd (list_fields fs))
  | Pparens p ->
     check_fvs p
  | Por (p, q) ->
     let p = check_fvs p in
     let q = check_fvs q in
     check_equ_fvs ploc p q

let check_fvs_mat loc = function
  | [] -> assert false
  | ps :: pps ->
     List.fold_left (check_equ_fvs loc)
       (check_fvs_list ps)
       (List.map check_fvs_list pps)
  

type ex_split = Ex : 'n dectree -> ex_split
let split_cases ~matchloc env (typs : ptyp list) (cases : case list) =
  let actions =
    cases |> List.mapi (fun id (pps, exp) ->
      let fvs = check_fvs_mat matchloc pps in
      { rhs = exp;
        id;
        bound = SymMap.map (fun _loc -> ref (Tcons Cons.bottom), fst (IR.Binder.fresh ())) fvs;
        used = false })
  in
  let Ex typs = Clist.of_list typs in
  let mat =
    List.map2 (fun (pps, _) b -> pps, b) cases actions
    |> List.concat_map (fun (pps, act) ->
      pps |> List.map (fun ps ->
        match Clist.of_list_length ~len:typs ps with
        | None -> failwith (*FIXME*)  "wrong length of pat row"
        | Some ps -> ps, (SymMap.empty, act)))
  in
  let table = Hashcons.fresh_table () in
  let dtree =
    split_cases ~table ~matchloc env SymMap.empty typs mat in
  let unmatched = counterexamples (Clist.map ignore typs) dtree in 
  let unmatched = List.map Clist.to_list unmatched in
  actions, Ex dtree, unmatched



module Compile_K = struct
  type 'w key = 'w dectree
  type 'w value = unit
  let equal = DectreeHash.equal_dectree
  let hash = DectreeHash.hash_dectree'
end
module Memo_compile = HashtblT (Compile_K)

(*

Which values should be passed along to shared continuations?
Do I need to compute the dominator tree?

To match dectree against vs, walk downwards collecting values
Shared subtree: track height of each?

Is it always a shared vtail?
Dectree operations are always on a prefix
But that can probably change?

Consider:
  | A(x, foo: P|Q), R
  | B(x, bar: P|Q), R

Shared subtree:
  P, R
  Q, R

reached after both A and B

yet the two applications of this subtree match different values

and it is not shared in the source language.

if I leave this unshared, I generate simpler code in most cases.
How to detect sharing purely of tails?

(1) Hashcons but mark tails somehow
(2) something smarter?

Could track paths in pattern matrices & key hashconsing off that?
Also produces reasonable domtrees

  | A(x, foo: P|Q), R
  | B(x, bar: P|Q), R

Alternatively, keep sharing as-is and pass the values along as needed.
Does this mean every continuation abstracts over all pattern variables?
I suppose I could compute dominator trees easily enough.

I need to precompute which variables each node abstracts over.
Maybe just compute the common prefix by hand?
It's fine for this not to be optimal!


AltAlt: just don't hashcons. Nahhhhhhh.

*)
(*
let rec compile ~table (type w) (dt : w dectree) (vals : (w, IR.value) Clist.t) =
  match Memo_table.find table dt with
  if Memo_compile.mem table dt 
*)
