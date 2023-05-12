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
  | Cases :
      (Typedefs.Cons.tuple_tag * 'n fields_split) list
      * ((Typedefs.Cons.tuple_tag * unit tuple_fields) list * 'n dectree) option -> 'n s dectree'
  | Fields : 'n fields_split -> 'n s dectree'

and 'n fields_split =
  | Proj : ('m, 'n, Tuple_fields.field_name) Clist.prefix * Tuple_fields.fields_open * 'm dectree -> 'n fields_split

module Hashcons = struct

  let is_empty : type a . a dectree' -> bool = function
    | Done _ -> false
    | Failure -> true
    | Any t -> t.empty
    | Bind (_, t) -> t.empty
    | Cases (cases, def) ->
       List.for_all (fun (_, Proj (_, _, fs)) -> fs.empty) cases
       &&
       (match def with Some (_, t) -> t.empty | None -> true)
    | Fields (Proj (_, _, fs)) -> fs.empty

  let is_total : type a . a dectree' -> bool = function
    | Done _ -> true
    | Failure -> false
    | Any t -> t.total
    | Bind (_, t) -> t.total
    | Cases (cases, def) ->
       List.for_all (fun (_, Proj (_, _, fs)) -> fs.total) cases
       &&
       (match def with Some (_, t) -> t.total | None -> true)
    | Fields (Proj (_, _, fs)) -> fs.total

  let mk (type n) (t : n dectree') : n dectree =
    { tree = t;
      empty = is_empty t;
      total = is_total t }
end

(* The result of splitting a (w+1)-size matrix along the first column *)
type 'w split_head =
  | Sp_any of 'w pat_matrix
  | Sp_fields of 'w split_fields
  | Sp_cases of tuple_tag list * 'w split_fields SymMap.t * 'w pat_matrix

and 'w split_fields =
  (pat tuple_fields Location.loc * 'w pat_row) list

let rec split_head_row :
  type w . _ -> w s pat_row -> IR.value IR.Binder.t option * w split_head -> IR.value IR.Binder.t option * w split_head
  = fun head_typ mat ((var, split) as acc) ->
  match mat with
  | ((None,loc) :: _ps), _act ->
     Error.fail loc Syntax
  | ((Some p,head_loc) :: ps), act ->
     match p with
     | Pparens p ->
        split_head_row head_typ ((p :: ps), act) acc
     | Por (p, q) ->
        let acc = split_head_row head_typ ((q :: ps), act) acc in
        let acc = split_head_row head_typ ((p :: ps), act) acc in
        acc
     | Pany ->
        let split =
          let no_fields fields =
            ((empty_fields, head_loc), (ps, act)) :: fields
          in
          match split with
          | Sp_any m ->
             Sp_any ((ps, act) :: m)
          | Sp_fields fields ->
             Sp_fields (no_fields fields)
          | Sp_cases (tags, cases, def) ->
             Sp_cases (tags,
                       SymMap.map no_fields cases,
                       (ps,act) :: def)
        in
        var, split
     | Ptuple (None, fields) ->
        let acc_fields =
          match split with
          | Sp_fields fields -> fields
          | Sp_any m -> List.map (fun r -> (empty_fields, []), r) m
          | Sp_cases (_tags, _cases, _def) ->
             Error.fail head_loc (Incompatible_patterns head_loc (* FIXME loc *))
        in
        let split = Sp_fields (((fields, head_loc), (ps, act)) :: acc_fields) in
        var, split
     | Ptuple (Some ((tag,_) as tagloc), fields) ->
        let acc_tags, acc_cases, acc_def =
          match split with
          | Sp_cases (tags, cases, def) -> tags, cases, def
          | Sp_any m -> [], SymMap.empty, m
          | Sp_fields _ ->
             Error.fail head_loc (Incompatible_patterns head_loc (*FIXME loc*))
        in
        let tail =
          try SymMap.find tag acc_cases
          with Not_found -> List.map (fun r -> (empty_fields, []), r) acc_def
        in
        var,
        Sp_cases (
            (if SymMap.mem tag acc_cases then acc_tags else tagloc :: acc_tags),
            SymMap.add tag (((fields, head_loc), (ps, act)) :: tail) acc_cases,
            acc_def)
     | Pvar (name, _) ->
        let var =
          match var with
          | None -> IR.Binder.fresh ~name ()
          | Some v -> v
        in
        let subpat = (Some Pany, head_loc) in
        let bindings, action = act in
        let ptyp, gen_level = head_typ in
        let bindings = SymMap.add name (ptyp, gen_level, var) bindings in
        let acc = Some var, split in
        split_head_row head_typ ((subpat :: ps), (bindings, action)) acc

let split_head head_typ (m : _ pat_matrix) =
  List.fold_right (split_head_row head_typ) m (None, Sp_any [])

let any : pat = (Some Pany, noloc)
let pat_or p q : pat = (Some (Por (p, q)), noloc)

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
                (fun name (typ, lvl, _var) -> typ, lvl, IR.Binder.fresh ~name ())
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
     let var, split = split_head (typ, lvl) mat in

     let collect_fields (fields : _ split_fields) =
       List.fold_left (fun (acc_loc, acc) ((fs, loc), _) ->
         acc_loc @ loc,
         (Tuple_fields.union acc fs
           ~left:(fun () -> ())
           ~right:(fun _ -> ())
           ~both:(fun () _ -> ())
         |> function
           | Some x -> x
           | None ->
              Error.fail loc (Incompatible_patterns acc_loc)) )
         ([], empty_fields)
         fields
     in

     let split_fields (ftypes : ptyp tuple_fields) (fields : _ split_fields) : _ fields_split =
       let fopen = ftypes.fopen in
       let Ex fs = Clist.of_list (list_fields ftypes |> List.map (fun (f, t) -> f, (t, lvl))) in
       let field_names = Clist.map fst fs in
       let field_types = Clist.map snd fs in
       let mat =
         fields
         |> List.map (fun (((pats, _loc), (row, act)) : pat tuple_fields Location.loc * _ pat_row) ->
            let lookup fn =
              match get_field_opt pats fn with
              | Some pat -> pat
              | None when pats.fopen = `Open -> any
              | None -> failwith "missing" (*FIXME possible?*)
            in
            Clist.append (Clist.map lookup field_names) row, act)
       in
       let tail = split_cases ~matchloc ~env (Clist.append field_types typs) mat in
       Proj (field_names, fopen, tail)
     in

     let dt =
       match split with
       | Sp_any mat ->
          let rest = split_cases ~matchloc ~env typs mat in
          Any rest
       | Sp_fields fields ->
          let loc, fnames = collect_fields fields in
          (* FIXME loc? *)
          let cons = Cons.Record(None, fnames) in
          begin match Types.match_typ env typ matchloc cons with
          | Ok (Record (_, ftypes)) ->
             let ftypes = map_fields (fun _ ((),t) -> t) ftypes in
             Fields (split_fields ftypes fields)
          | Ok _ -> assert false
          | Error e -> Error.fail loc (Conflict (`Pat, e))
          end
       | Sp_cases (tags, cases, def) ->
          let extract_cases = function
            | Tcons {conses; _} ->
               conses
               |> List.map (function
                 | Cons.Record (Some tag, fields) -> tag, fields
                 | _ -> raise Exit)
               |> List.to_seq
               |> SymMap.of_seq
            | _ -> raise Exit
          in
          match extract_cases typ with
          | case_types ->
             let default_tags = ref [] in
             let cases =
               SymMap.merge
                 (fun tag typ fields ->
                   match typ, fields with
                   | None, None -> None
                   | Some typ, None ->
                      default_tags :=
                        (tag, map_fields (fun _fn _ -> ()) typ) :: !default_tags;
                      None
                   | None, Some _ ->
                      failwith "unknown ctor"
                               (*
                      Error.fail matchloc(*FIXME*)
                        (Illformed_pat (`Unknown_constructor tag)); *)
                   | Some typ, Some fields ->
                      Some (split_fields typ fields))
                 case_types cases
             in
             let cases =
               tags |> List.map (fun (tag,_) ->
                 tag, SymMap.find tag cases)
             in
             let defaults =
               match !default_tags with
               | [] -> None
               | default_tags ->
                  Some (default_tags,
                        split_cases ~matchloc ~env typs def)
             in
             Cases (cases, defaults)
          | exception Exit ->
             begin match def with
             | [] -> ()
             | row :: _ ->
                Error.fail Location.noloc(*FIXME*) (Illformed_pat `Unknown_cases)
             end;
             let inferred_cases =
               cases |>
               SymMap.map (fun fields ->
                 let loc, fnames = collect_fields fields in
                 let fields = map_fields (fun _ () -> ref (Tcons Cons.bottom)) fnames in
                 loc, fields)
             in
             let loc =
               tags |> List.concat_map (fun (tag,_) ->
                 fst (SymMap.find tag inferred_cases)) in
             let conses =
               tags |> List.map (fun (tag,_) ->
                 let _, fields = SymMap.find tag inferred_cases in
                 Cons.Record(Some tag, fields)) in
             let cons = Cons.make' ~loc conses in
             begin match Types.match_typ2 env typ cons with
             | Ok () -> ()
             | Error e -> Error.fail matchloc (Conflict (`Pat, e))
             end;
             let case_list =
               tags
               |> List.map (fun (tag,_) ->
                  let (loc, fields) = SymMap.find tag inferred_cases in
                  let fields = map_fields (fun _ r -> !r) fields in
                  let case = SymMap.find tag cases in
                  tag, split_fields fields case)
             in
             Cases (case_list, None)
     in
     let dt =
       match var with
       | Some v -> Bind (v, Hashcons.mk dt)
       | None -> dt
     in
     Hashcons.mk dt


let rec counterexamples :
  type n . (n, _) Clist.t -> n dectree -> (n, pat) Clist.t list =
  fun len dt ->
  if dt.total then []
  else if dt.empty then [Clist.map (fun _ -> any) len]
  else match len, dt.tree with
  | [], _ -> assert false (* zero len means dt must be empty or total *)
  | _ :: _ as len, Bind (_, dt) -> counterexamples len dt
  | _ :: len, Any dt ->
     counterexamples len dt
     |> List.map (fun ps -> Clist.(any :: ps))
  | _ :: len, Fields fields ->
     counterexamples_fields ~tag:None len fields
  | _ :: len, Cases (cases, defaults) ->
     List.concat_map (fun (tag, fields) ->
       counterexamples_fields ~tag:(Some (tag, noloc)) len fields) cases
     @
     match defaults with
     | Some (tags, dt) when not dt.total ->
        let case_pats : pat list =
          List.map (fun (tag, fields) ->
             Some (Ptuple (Some (tag, noloc),
                           map_fields (fun _ () -> any) fields)), noloc) tags
        in
        let head = List.fold_left pat_or (List.hd case_pats) (List.tl case_pats) in
        counterexamples len dt
        |> List.map (fun ps -> Clist.(head :: ps))
     | _ -> []

and counterexamples_fields :
  type n . tag:_ -> (n, _) Clist.t -> n fields_split -> (n s, pat) Clist.t list =
  fun ~tag len (Proj (names, fopen, dt)) ->
  counterexamples (Clist.append (Clist.map ignore names) len) dt
  |> List.map (fun unmatched ->
    let fs, rest = Clist.split names len unmatched in
    let fields =
      Clist.zip names fs
      |> Clist.to_list
      |> Tuple_fields.fields_of_list ~fopen
    in
    Clist.((Some (Ptuple (tag, fields)), noloc) :: rest))


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
      then Some (IR.Binder.fresh ~name:"case" (),
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
    | Cases (cases, default), v :: vals ->
       let cases =
         cases |> List.map (fun (tag, fs) ->
           let cont = compile_fields ~vals fs in
           IR.Symbol.of_string tag, cont)
       in
       let default =
         default |> Option.map (fun (tags, dt) ->
           List.map (fun (tag,_fs) -> IR.Symbol.of_string tag) tags,
           compile ~vals dt)
       in
       Match (v, cases, default)
    | Fields fs, v :: vals ->
       Project (v, compile_fields ~vals fs)

  and compile_fields :
    type w . vals:(w, IR.value) Clist.t -> w fields_split -> IR.unpacking_cont =
    fun ~vals (Proj (fs, _op, dt)) ->
    let vname : Tuple_fields.field_name -> string = function
      | Field_named s -> s
      | Field_positional n -> Printf.sprintf "v%d" n
    in
    let field_vars = Clist.map (fun name -> name, IR.Binder.fresh ~name:(vname name) ()) fs in
    let binders = field_vars in
    let field_vars = Clist.map (fun (_,v) -> IR.var v) field_vars in
    let vals = Clist.append field_vars vals in
    let rest = compile ~vals dt in
    Clist.to_list binders, rest

  in
  let Ex (len, dt) = orig_dt in
  let vals = Option.get (Clist.of_list_length ~len vals) in
  let code = compile ~vals dt in
  List.fold_right
    (fun act acc ->
      match act.rhs with
      | None, _ -> acc
      | Some (label, names), body ->
         IR.LetCont (label, List.map snd names, body, acc))
    (Array.to_list actions)
    code
