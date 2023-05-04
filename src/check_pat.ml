open Exp
open Typedefs
open Tuple_fields
open Util

type bindings = (ptyp * Typedefs.gen_level * IR.value IR.Binder.t) SymMap.t

type 'rhs action = {
  rhs: 'rhs;
  id: int;
  pat_loc: Location.t;
  mutable bindings: bindings;
  mutable refcount: int;
}

type 'w pat_row = ('w, pat) Clist.t * (bindings * exp action)

type 'w pat_matrix = 'w pat_row list

open Peano_nat_types
type 'n dectree =
  { tree: 'n dectree';
    empty: bool;
    total: bool }

and _ dectree' =
  | Done : IR.value IR.Binder.t SymMap.t * exp action -> z dectree'
  | Failure : z dectree'
  | Any : 'n dectree -> 'n s dectree'
  | Bind : IR.value IR.Binder.t * 'n s dectree -> 'n s dectree'
  (* Cases: nonempty and sorted *)
  | Cases : (Typedefs.Cons.tuple_tag * 'n fields_split) list -> 'n s dectree'
  | Fields : 'n fields_split -> 'n s dectree'

and 'n fields_split =
  | Proj : ('m, 'n, Tuple_fields.field_name) Clist.prefix * Tuple_fields.fields_open * 'm dectree -> 'n fields_split

module Hashcons = struct

  let is_empty : type a . a dectree' -> bool = function
    | Done _ -> false
    | Failure -> true
    | Any t -> t.empty
    | Bind (_, t) -> t.empty
    | Cases cases -> List.for_all (fun (_, Proj (_, _, fs)) -> fs.empty) cases
    | Fields (Proj (_, _, fs)) -> fs.empty

  let is_total : type a . a dectree' -> bool = function
    | Done _ -> true
    | Failure -> false
    | Any t -> t.total
    | Bind (_, t) -> t.total
    | Cases cases -> List.for_all (fun (_, Proj (_, _, fs)) -> fs.total) cases
    | Fields (Proj (_, _, fs)) -> fs.total

  let mk (type n) (t : n dectree') : n dectree =
    { tree = t;
      empty = is_empty t;
      total = is_total t }
(*
  let rec same_values : type n . n dectree -> n dectree -> bool =
    fun a b ->
    match a.tree, b.tree with
    | Done _, Done _ -> true
    | Failure _, Failure _ -> true
    | Any _, Any _ -> true
*)

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
  else if List.for_all (function {head=Hany | Hfields _; _} -> true | {head=Hcase _; _} -> false) heads then
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
      Types.match_typ env ty matchloc fields
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

let row_tail ~binding typ gen_level row : _ pat_row =
  match row.var, row.rest with
  | None, rest -> rest
  | Some v, (pats, (bindings, act)) ->
     (pats, (SymMap.add v (typ, gen_level, Option.get binding) bindings, act))


let rec split_cases :
  type w . matchloc:_ -> env:_ -> (w, ptyp * Typedefs.gen_level) Clist.t -> w pat_matrix -> w dectree =
  fun ~matchloc ~env typs mat ->
  match typs with
  | [] ->
     begin match mat with
     | [] ->
        Hashcons.mk Failure
     | ([], (bindings, act)) :: _ ->
        (* We have already checked that all paths to
           the same action bind the same vars *)
        act.refcount <- act.refcount + 1;
        if act.refcount = 1 then begin
          assert (SymMap.is_empty act.bindings);
          act.bindings <- bindings;
        end else begin
          let old_bindings =
            if act.refcount > 2 then act.bindings
            else
              SymMap.mapi
                (fun name (typ, lvl, _var) -> typ, lvl, fst (IR.Binder.fresh ~name ()))
                act.bindings
          in
          act.bindings <-
            old_bindings
            |> SymMap.mapi (fun name (typ, lvl, var) ->
                   Types.join_ptyp env typ (let (ty,_,_) = (SymMap.find name bindings) in ty),
                   lvl,
                   var)
        end;
        Hashcons.mk (Done (SymMap.map (fun (_,_,v) -> v) bindings, act))
     end

  | (typ, lvl) :: typs ->
     let mat = peel_pat_heads mat in
     let binding =
       let all_bound =
         List.concat_map (fun r -> Option.to_list r.var) mat in
       match all_bound with
       | [] -> None
       | name :: _ ->
          let v, _ = IR.Binder.fresh ~name () in
          Some v
     in

     let split_fields ~tag fs mat =
        let fopen = fs.fopen in
        let Ex fs = Clist.of_list (list_fields fs |> List.map (fun (f,t) -> f, (t, lvl))) in
        let field_names = Clist.map fst fs in
        let field_types = Clist.map snd fs in
        let mat = List.map (read_fields ~tag field_names) mat in
        let rest =
          split_cases ~matchloc ~env (Clist.append field_types typs) mat in
        Proj (field_names, fopen, rest)
     in

     let dt =
       match decide_split_kind ~matchloc env typ mat with
       | Sany ->
          let rest = split_cases ~matchloc ~env typs (List.map (row_tail ~binding typ lvl) mat) in
          Any rest
       | Sfields fs ->
          let fs = split_fields ~tag:None fs mat in
          Fields fs
       | Scases cases ->
          let cases = SymMap.mapi (fun tag fs ->
            let mat = List.filter (matches_tag tag) mat in
            split_fields ~tag:(Some tag) fs mat) cases in
          let cases = SymMap.to_seq cases |> List.of_seq in
          Cases cases
     in

     let dt =
       match binding with
       | Some v ->
          Bind (v, Hashcons.mk dt)
       | None ->
          dt
     in
     Hashcons.mk dt
     

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

let equal_dectree a b =
  (* FIXME: is this a good enough approx for counterexamples? *)
  (a.total && b.total)
  ||
  (a.empty && b.empty)

let rec dectree_tails : type n k. (n, k, unit) Clist.prefix -> n dectree -> k dectree option =
  fun pfx t ->
  (* FIXME: same results with equal = false?! *)
  let unique_dt f xs =
    find_map_unique ~equal:(fun a b -> equal_dectree a b) f xs in

  match pfx, t.tree with
  | [], _ -> Some t
  | _ :: pfx, Any tail ->
     dectree_tails pfx tail
  | _ :: _ as pfx, Bind (_, tail) ->
     dectree_tails pfx tail
  | _ :: pfx, Cases cases ->
     cases |> unique_dt (fun (_, Proj (fs, _, t)) ->
       dectree_tails (Clist.append (Clist.map ignore fs) pfx) t)
  | _ :: pfx, Fields (Proj (fs, _, t)) ->
     dectree_tails (Clist.append (Clist.map ignore fs) pfx) t


let counterexamples depth t =
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
    | _ :: pfx as orig_pfx ->
       match dectree_tails [()] dt with
       | Some tail ->
          (* head must be total! *)
          let ex = examples pfx tail in
          List.map (fun ps -> Clist.(any :: ps)) ex
       | None ->
          match dt.tree with
          | Any _ -> assert false (* has tail *)
          | Bind (_, t) -> examples orig_pfx t
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
                      | (_, _, Some tail') when equal_dectree tail tail' ->
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
  

type ex_split = Ex : (('n,_) Clist.t * 'n dectree) -> ex_split
let split_cases ~matchloc env (typs : (ptyp * Typedefs.gen_level) list) (cases : case list) =
  let actions =
    cases |> List.mapi (fun id ((pps,pat_loc), exp) ->
      let _fvs = check_fvs_mat matchloc pps in
      { rhs = exp;
        pat_loc;
        id;
        bindings = SymMap.empty; (* FIXME types are poor here *)
        refcount = 0 })
  in
  let Ex typs = Clist.of_list typs in
  let mat =
    List.map2 (fun (pps, _) b -> pps, b) cases actions
    |> List.concat_map (fun ((pps,_loc), act) ->
      pps |> List.map (fun ps ->
        match Clist.of_list_length ~len:typs ps with
        | None -> failwith (*FIXME*)  "wrong length of pat row"
        | Some ps -> ps, (SymMap.empty, act)))
  in
  let dtree = split_cases ~matchloc ~env typs mat in
  actions |> List.iter (fun act ->
    if act.refcount = 0 then
      Error.log ~loc:act.pat_loc Unused_pattern);
  begin match counterexamples (Clist.map ignore typs) dtree with
  | [] -> ()
  | unmatched ->
     Error.log ~loc:matchloc (Nonexhaustive (List.map Clist.to_list unmatched))
  end;
  actions, Ex (typs, dtree)

(* FIXME: Check dedups cont. Should that happen here instead? *)
let compile ~cont ~actions vals orig_dt =
  let actions = actions |> Array.map (fun act ->
    let label =
      if act.refcount >= 2
      then Some (fst (IR.Binder.fresh ~name:"case" ()),
                 List.map (fun (name, (_ty, _lvl, var)) -> name, var) (SymMap.bindings act.bindings))
      else None
    in
    { act with rhs = (label, act.rhs cont) })
  in

  let rec compile :
     type w . vals:(w, IR.value) Clist.t -> w dectree -> IR.comp =
    fun ~vals dt -> compile_tree ~vals dt.tree
  and compile_tree :
     type w . vals:(w, IR.value) Clist.t -> w dectree' -> IR.comp =
    fun ~vals dt ->
    match dt, vals with
    | Done (bindings, act), [] ->
       (* FIXME bind the variables properly *)
       assert (act.refcount > 0);
       begin match actions.(act.id).rhs with
       | Some (label, vars), _body ->
          Jump (IR.Binder.ref label,
                List.map (fun (v,_) -> IR.Var (IR.Binder.ref (SymMap.find v bindings))) vars)
       | None, body ->
          body
       end
    | Failure, [] ->
       (* FIXME better error *)
       IR.Trap "match failure"
    | Any dt, _ :: vals ->
       compile ~vals dt
    | Bind (var, dt), (v :: _ as vals) ->
       LetVal (var, v, compile ~vals dt)
    | Cases cases, v :: vals ->
       let cases =
         cases |> List.map (fun (tag, fs) ->
           let fields, cont = compile_fields ~vals fs in
           IR.Symbol.of_string tag, fields, cont)
       in
       Match (v, cases)
    | Fields fs, v :: vals ->
       let fields, cont = compile_fields ~vals fs in
       Project (v, fields, cont)

  and compile_fields :
    type w . vals:(w, IR.value) Clist.t -> w fields_split -> field_name list * IR.cont =
    fun ~vals (Proj (fs, _op, dt)) ->
    let vname : Tuple_fields.field_name -> string = function
      | Field_named s -> s
      | Field_positional n -> Printf.sprintf "v%d" n
    in
    let field_vars = Clist.map (fun name -> IR.Binder.fresh ~name:(vname name) ()) fs in
    let binders = Clist.map (fun (v, _) -> v) field_vars in
    let field_vars = Clist.map (fun (_, v) -> IR.Var v) field_vars in
    let vals = Clist.append field_vars vals in
    let rest = compile ~vals dt in
    Clist.to_list fs, Cont (Clist.to_list binders, rest)

  in
  let Ex (len, dt) = orig_dt in
  let vals = Option.get (Clist.of_list_length ~len vals) in
  let code = compile ~vals dt in
  List.fold_right
    (fun act acc ->
      match act.rhs with
      | None, _ -> acc
      | Some (label, names), body ->
         IR.LetCont (label, Cont (List.map snd names, body), acc))
    (Array.to_list actions)
    code
