open Exp
open Typedefs
open Util

module FieldMap = Tuple_fields.FieldOrdMap

module List = struct
  include List

  (* Like partition_map, but elements can go on both sides *)
  let rec split_filter_map f = function
    | [] -> [], []
    | x :: xs ->
       let l, r = f x in
       let ls, rs = split_filter_map f xs in
       (match l with
        | None -> ls
        | Some l -> l :: ls),
       (match r with
        | None -> rs
        | Some r -> r :: rs)
end

module Fields = Typedefs.Fields

module TagMap = Typedefs.Cons1.Tag.Map

(* FIXME: move somewhere new? *)
type mand_flag =
  | Mandatory
  | Optional

type pat_head =
  | Ph_tuple of Typedefs.Cons1.Tag.t * pat fields
  | Ph_any

type split_kind =
  | Split_none
  | Split_any
  | Split_cases of (mand_flag loc FieldMap.t * Exp.extensible_flag * Location.t) TagMap.t * Exp.extensible_flag loc

(* FIXME: move to Types? *)
let ptyp_conses ~env (t : ptyp) =
  let rec go = function
    | Tcvj (conses, [], _) ->
       List.map (function
         | (Cons1.Record ({tag=Some tag; _} as r)),loc -> tag,(r,loc)
         | _ -> raise Exit) conses
    | Tcvj (conses, (rv :: rvs), loc) ->
       go (Types.join_ptyp env
             (Tcvj (conses, rvs, loc))
             (Types.ptyp_of_rigid_bound env (Types.as_rigvar rv)))
    | _ -> raise Exit
  in
  match go t with
  | exception Exit -> None
  | t -> Some t

let split_kind (pats : pat_head loc list) : split_kind =
  let find_cases : pat_head loc -> _ = function
    | Ph_any, loc ->
       Either.Left loc
    | Ph_tuple (tag, fields), loc ->
       let fields =
         Exp.record_fields ~loc fields
         |> List.map (fun ((fn,loc),pat) -> fn,(loc,pat))
         |> FieldMap.of_multi_list
              ~merge:(fun fn (loc',_pat') (loc,_pat) ->
                let name = Tuple_fields.string_of_field_name fn in
                Error.fail loc (Illformed_pat (`Duplicate_name (`Field, name, loc'))))
         |> FieldMap.map
              ~f:(fun (loc,pat) ->
                let mand =
                  match pat with
                  | Exp.Optional _ | Exp.Absent -> Optional
                  | Exp.Mandatory _ -> Mandatory
                  | Exp.Abs_broken ->
                     (* FIXME better error? *)
                     Error.fail loc Syntax
                in
                (mand, loc))
       in
       Either.Right (tag, (fields, Ext_closed, loc))
  in
  match List.partition_map find_cases pats with
  | [], [] -> Split_none
  | (_::_), [] -> Split_any
  | wildcard, cases ->
    let merge _tag (fields1, ex1, loc1) (fields2, ex2, loc2) =
      let ex, loc =
        match ex1, ex2 with
        | Ext_open, Ext_open -> Ext_open, loc1
        | Ext_open, Ext_closed -> Ext_closed, loc2
        | Ext_closed, Ext_open -> Ext_closed, loc1
        | Ext_closed, Ext_closed -> Ext_closed, loc1
      in
      FieldMap.merge fields1 fields2
        ~f:(fun _fn f1 f2 ->
          match f1, f2 with
          | None, None
          | Some (Mandatory, _), Some (Mandatory, _)
          | Some (Optional, _), Some (Optional, _) -> f1
          | Some _, None when ex2 = Ext_open -> f1
          | None, Some _ when ex1 = Ext_open -> f2
          | f1, f2 ->
             let loc1 = match f1 with Some (_,l) -> l | None -> loc1 in
             let loc2 = match f2 with Some (_,l) -> l | None -> loc2 in
             Error.fail loc1 (Incompatible_patterns loc2)),
      ex,
      loc
    in
    let case_map = TagMap.of_multi_list ~merge cases in
    let ext = match wildcard with loc::_ -> Ext_open, loc | [] -> Ext_closed, (Location.fixme "unneeded?") in
    Split_cases (case_map, ext)

type split_type =
  | Split_type_any
  | Split_type_cases of split_type_cases

and split_type_cases = (Cons1.Tag.t * split_type_field list) list

and split_type_field =
  (Tuple_fields.field_name * mand_flag * ptyp)


let split_type ~env ~matchloc (t : ptyp) (kind : split_kind) : split_type =
  match kind with
  | Split_none | Split_any -> Split_type_any
  | Split_cases (cases, (ext, extloc)) ->
     let split_fields fields =
       let fields = FieldMap.map ~f:(fun (mand,loc) -> mand, loc, ref (tbot (Some loc))) fields in
       let tybody =
         fields
         |> FieldMap.map ~f:(function
           | Mandatory, loc, ty ->
              Fields.Fpresent (ty, loc)
           | Optional, loc, ty ->
              let loc = Fields.{pres_loc=loc; abs_loc=loc} in
              Fields.Foptional (ty, loc) )
         |> FieldMap.to_list
         |> Fields.of_list
       in
       let split () =
         fields
         |> FieldMap.to_list
         |> List.map (fun (name, (mand, _loc, ty)) -> name, mand, !ty)
       in
       tybody, split
     in
     let check_fields ~env ~loc ((cons : _ Cons1.cons_record),cons_loc) (fields_b,ext) =
       let decl_fields =
         match cons.tag with
         | Some (Named_tag t) -> Env.get_decl_fields env t
         | None | Some (Anon_tag | Struct_tag _) -> Fields.empty
       in
       let fields_a = cons.body in
       let ext_a = Types.Cons1.record_def ~env ~shape:(Types.Type_shape.gen_pos) ~loc:cons_loc cons in
       let ext_b _ = Fields.desc_of_ext loc ext in
       match
         Types.Fields.sub ~extra:decl_fields (fields_a,ext_a) (fields_b, ext_b)
           ~f:(fun _k a b -> b := a)
       with
       | Ok () -> ()
       | Error (err : Types.Fields.field_error) ->
          let err, cploc, cnloc =
            match err with
            | Field_missing (name, ploc, nloc) ->
               Types.Field_missing name, ploc, nloc
            | Field_extra (name, ploc, nloc) ->
               Types.Field_extra name, ploc, nloc
          in
          let cp = Cons1.Record cons in
          (* drop tag to avoid making invalid args *)
          let tag = match cons.tag with Some (Anon_tag | Struct_tag _) as t -> t | _ -> None in
          let cn = Cons1.Record{tag; args=[]; body=fields_b} in
          let err = Types.make_err env err (cp, cploc) (cn, cnloc) in
          Error.fail loc (Conflict (`Pat, err))
     in
     (* Checked conses should be used for:
          - filling in wildcards
          - looking up tags in the right namespace
          - more? *)
     let splits =
       match ptyp_conses ~env t with
       | Some checking_conses ->
          TagMap.merge cases (TagMap.of_list checking_conses)
            ~f:(fun _tag case ck ->
              match case, ck with
              | None, None -> None
              | Some _, None ->
                 (* Drop this case, it's impossible *)
                 None
              | Some (fields, ext, loc), Some ty ->
                 let fields, split = split_fields fields in
                 check_fields ~env ~loc ty (fields,ext);
                 Some split
              | None, Some (_ty, _tyloc) ->
                 (* No error here: the unhandled cases will be reported as
                    nonexhaustive matches by counterexample generation later. *)
                 Some (fun () -> []) (*FIXME should be Ext_open?*))
          |> TagMap.to_list
       | None ->
          (* Infer type of patterns *)
          if ext = Ext_open then Error.fail extloc (Illformed_pat `Unknown_cases);
          let conses, delayed_splits =
            TagMap.to_list cases
            |> List.map (fun ((tag:Cons1.Tag.t), (fields, ext, loc)) ->
               if ext = Ext_open then
                 (* FIXME test *)
                 Error.fail loc (Illformed_pat `Unknown_fields);
               match tag with
               | Anon_tag | Struct_tag _ ->
                  let tybody, split = split_fields fields in
                  Cons1.Record {tag = Some tag; args = []; body = tybody},
                  (tag, split)
               | Named_tag name ->
                  (* FIXME: check whether invariant params need to be
                     related. I think not, that's only for intro forms? *)
                  let args =
                    Env.get_decl_params env name
                    |> List.map (fun (var, _) : _ Cons1.tyarg ->
                      Cons1.Tyarg.of_variance_spec var
                      |> Cons1.Tyarg.map
                           ~neg:(fun () -> ref (ttop loc))
                           ~pos:(fun () -> ref (tbot (Some loc))))
                  in
                  let fields, split = split_fields fields in
                  let cons : _ Cons1.cons_record =
                    { tag = Some tag; args; body = Fields.empty } in
                  Cons1.Record cons,
                  (tag, (fun () ->
                    let cons = Cons1.cons_record_map ~neg:(!) ~pos:(!) cons in
                    check_fields ~env ~loc (cons,Nom_tag.loc name) (fields, ext);
                    split ())))
            |> List.split
          in
          begin match Types.match_ptyp ~loc:matchloc env t conses with
          | Ok () -> ()
          | Error  e -> Error.fail matchloc (Conflict (`Pat, e))
          end;
          delayed_splits
     in
     Split_type_cases (List.map (fun (t, s) -> t, s ()) splits)

let split_case tag (splits : split_type_cases) : split_type_field list * split_type_cases =
  match List.partition (fun (t,_) -> Cons1.tuple_tag_equal t tag) splits with
  | [_, c], splits -> c, splits
  | _ -> intfail "split_case: no such case"


type bindings = Typedefs.value_binding SymMap.t

type shared_cont = (IR.cont IR.Binder.t * (string * IR.value IR.Binder.t) list)

type act_bindings =
  { bindings: bindings;
    shared_cont: shared_cont option }

type 'rhs action = {
  rhs: 'rhs;
  id: int;
  pat_loc: Location.t;
  mutable bindings: act_bindings option;
}

type 'w pat_row = ('w, pat) Clist.t * (bindings * exp action)

type 'w pat_matrix = 'w pat_row list
open Peano_nat_types


type 'w head_pat_row = pat_head loc * 'w pat_row
type 'w head_pat_matrix = 'w head_pat_row list

let check_tag ~loc ~env typ (etag : Exp.tuple_tag) : Cons1.Tag.t =
  match etag with
  | Anon_tag ->
     Anon_tag
  | Struct_tag s ->
     Struct_tag s
  | Qualified_tag (s,t) ->
     begin match Env.lookup_decl env (fst s) with
     | None -> Error.fail (snd s) (Bad_name (`Unknown, `Type, fst s))
     | Some {body = Decl_record _ | Decl_primitive; _} ->
        Error.fail (snd s) (Bad_name (`Expected `Variant, `Type, fst s))
     | Some {body = Decl_variant vs; _} ->
        match SymLocMap.find_opt t vs with
        | None -> Error.fail (snd t) (Bad_name (`Unknown, `Type, fst s ^ "." ^ fst t))
        | Some _ ->
           Named_tag (Variant_tag (s,t))
     end
  | Named_tag t ->
     match ptyp_conses ~env typ with
     | None ->
        begin match Env.lookup_decl env (fst t) with
        | None -> Error.fail (snd t) (Bad_name (`Unknown, `Type, fst t))
        | Some {body = Decl_primitive | Decl_variant _; _} ->
           Error.fail (snd t) (Bad_name (`Expected `Record, `Type, fst t))
        | Some {body = Decl_record _; _} -> Named_tag (Record_tag t)
        end
     | Some conses ->
        (* FIXME: should an unexpected tag be ignored with a warning instead? *)
        let tags = List.map fst conses in
        match List.filter (Cons1.Tag.matches etag) tags with
        | [t] -> t
        | _ -> Error.fail loc (Bad_tag (Some etag, List.map Cons1.Tag.unparse tags))

let head_first_column ~env (typ,gen_level) mat =
  let rec go ~var (mat : 'w s pat_matrix) :
      'w head_pat_matrix * IR.value IR.Binder.t option =
    match mat with
    | [] -> [], var
    | ((None, loc) :: _row, _act) :: _ -> Error.fail loc Syntax
    | ((Some p, loc) :: row, act) :: rest ->
       match p with
       | Por (p, q) ->
          go ~var ((p::row,act)::(q::row,act)::rest)
       | Ptuple (None, _) ->
          Error.fail loc (Illformed_pat `Tag_required)
       | Pbind ((name,_), p) ->
          let var =
            match var with
            | None -> IR.Binder.fresh ~name ()
            | Some v -> v
          in
          let bindings, action = act in
          let bindings = SymMap.add name {typ; gen_level; comp_var = IR.Binder.ref var } bindings in
          go ~var:(Some var) (((p::row),(bindings,action))::rest)
       | Ptuple (Some tag, fs) ->
          let tag = check_tag ~loc ~env typ tag in
          let rest, var = go ~var rest in
          (((Ph_tuple(tag,fs),loc), (row,act))::rest),var
       | Pany ->
          let rest, var = go ~var rest in
          (((Ph_any,loc), (row,act))::rest), var
  in
  go ~var:None mat

let pvar s = Pbind (s, (Some Pany, snd s))

let split_on_case (type k w) tag (fields : (k, split_type_field) Clist.t) (mat : w head_pat_matrix) : ((k,pat Exp.exp_field option) Clist.t * w pat_row) list * w head_pat_matrix =
  mat |> List.split_filter_map (fun orig_row ->
    let (p, ploc), row = orig_row in
    match p with
    | Ph_tuple (tag', fs) when Cons1.tuple_tag_equal tag tag' ->
       let fs = Exp.record_fields ~loc:ploc fs in
       let fs =
         fields |> Clist.map (fun (fn,_mand,_ty) ->
           match
             List.find_opt (fun ((fn',_),_) ->
               Tuple_fields.equal_field_name fn fn') fs
           with
           | None -> None
           | Some ((_,floc), pat) ->
             Some (pat |> Exp.map_exp_field (function
               | Some p -> p
               | None -> Some (pvar (Tuple_fields.string_of_field_name fn, floc)), floc)))
       in
       Some (fs, row), None
    | Ph_tuple _ ->
       None, Some orig_row
    | Ph_any ->
       let fs = fields |> Clist.map (fun _ -> None) in
       Some (fs, row), Some orig_row)

type 'n dectree =
  { tree: 'n dectree';
    empty: bool;
    total: bool }

and _ dectree' =
  | Done : IR.value IR.Binder.ref SymMap.t * exp action -> z dectree'
  | Failure : z dectree'
  | Any : 'n dectree -> 'n s dectree'
  | Bind : IR.value IR.Binder.t * 'n s dectree -> 'n s dectree'
  (* Cases: nonempty and sorted *)
  | Cases :
      (Typedefs.Cons1.tuple_tag * 'n field_projections) list
      * (Typedefs.Cons1.tuple_tag list * 'n dectree) option -> 'n s dectree'

and 'n field_projections =
  (* Outermost Proj_foo: rightmost column (reverse order) *)
  | Proj_end of 'n dectree
  | Proj_mand of Tuple_fields.field_name * 'n s field_projections
  | Proj_opt of Tuple_fields.field_name * 'n s field_projections * 'n field_projections

module Hashcons = struct

  let rec is_empty_fields : type a . a field_projections -> bool = function
    | Proj_end t -> t.empty
    | Proj_mand (_,fs) -> is_empty_fields fs
    | Proj_opt (_,fs,fs') -> is_empty_fields fs && is_empty_fields fs'

  let is_empty : type a . a dectree' -> bool = function
    | Done _ -> false
    | Failure -> true
    | Any t -> t.empty
    | Bind (_, t) -> t.empty
    | Cases (cases, def) ->
       List.for_all (fun (_,fs) -> is_empty_fields fs) cases
       &&
       (match def with Some (_, t) -> t.empty | None -> true)

  let rec is_total_fields : type a . a field_projections -> bool = function
    | Proj_end t -> t.total
    | Proj_mand (_,fs) -> is_total_fields fs
    | Proj_opt (_,fs,fs') -> is_total_fields fs && is_total_fields fs'

  let is_total : type a . a dectree' -> bool = function
    | Done _ -> true
    | Failure -> false
    | Any t -> t.total
    | Bind (_, t) -> t.total
    | Cases (cases, def) ->
       List.for_all (fun (_, fs) -> is_total_fields fs) cases
       &&
       (match def with Some (_, t) -> t.total | None -> true)

  let mk (type n) (t : n dectree') : n dectree =
    { tree = t;
      empty = is_empty t;
      total = is_total t }
end


let any : pat = (Some Pany, Location.noloc)
let pat_or p q : pat = (Some (Por (p, q)), Location.noloc)

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
        act.bindings <-
          (match act.bindings with
          | None ->
             (* First use of action *)
             Some { bindings; shared_cont = None }
          | Some { bindings = prev_bindings; shared_cont } ->
             let prev_bindings, shared_cont =
               match shared_cont with
               | Some _ ->
                  prev_bindings, shared_cont
               | None ->
                  let cont = IR.Binder.fresh ~name:"case" () in
                  let freshened =
                    SymMap.mapi (fun name x -> IR.Binder.fresh ~name (), x) prev_bindings in
                  SymMap.map (fun (v, vb) -> {vb with comp_var = IR.Binder.ref v}) freshened,
                  Some (cont,
                        SymMap.bindings freshened
                        |> List.map (fun (name, (v, _)) -> name,v))
             in
             let bindings =
               prev_bindings
               |> SymMap.mapi (fun name vb ->
                  { vb with
                    typ =
                      Types.join_ptyp env vb.typ
                        (SymMap.find name bindings).typ })
             in
             Some {bindings; shared_cont});
        Hashcons.mk (Done (SymMap.map (fun vb -> vb.comp_var) bindings, act))
     end

  | (typ, lvl) :: typs ->
     let mat, var = head_first_column ~env (typ,lvl) mat in
     let sk = split_kind (List.map fst mat) in
     let split_ty = split_type ~env ~matchloc typ sk in
     let dt =
       match split_ty with
       | Split_type_any ->
          let mat = List.map snd mat in
          let rest = split_cases ~matchloc ~env typs mat in
          Any rest
       | Split_type_cases cases ->
          let rec proj : type k w .
            (k, split_type_field) Clist.t ->
            (w, ptyp * gen_level) Clist.t ->
            ((k,pat exp_field option) Clist.t * w pat_row) list ->
            w field_projections =
            fun ftyps typs pats ->
            match ftyps with
            | [] ->
               Proj_end (split_cases ~matchloc ~env typs (List.map snd pats))
            | (fname, Mandatory, ty) :: ftyps ->
               let pats =
                 pats |> List.map (fun (fs, ((row,act) : w pat_row)) ->
                   let fpat = Clist.hd fs and fs = Clist.tl fs in
                   let pat =
                     match fpat with
                     | Some (Exp.Mandatory p) -> p
                     | Some _ -> intfail "bad fpat kind"
                     | None -> Some Pany, matchloc
                   in
                   fs, (Clist.(pat :: row), act))
               in
               Proj_mand (fname, proj ftyps ((ty,lvl)::typs) pats)
            | (fname, Optional, ty) :: ftyps ->
               let pats_pres, pats_abs =
                 pats |> List.split_filter_map (fun (fs, ((row,act) : w pat_row)) ->
                   let fpat = Clist.hd fs and fs = Clist.tl fs in
                   match fpat with
                   | Some (Exp.Mandatory _) -> intfail "bad fpat kind"
                   | Some (Exp.Optional p) ->
                      Some (fs, (Clist.(p::row), act)), None
                   | Some (Exp.Absent | Exp.Abs_broken) ->
                      None, Some (fs, (row,act))
                   | None ->
                      let pany = Some Pany, Location.noloc in
                      Some (fs, (Clist.(pany::row), act)),
                      Some (fs, (row, act)))
               in
               Proj_opt (fname,
                         proj ftyps ((ty,lvl)::typs) pats_pres,
                         proj ftyps typs pats_abs)
          in

          let rec split cases mat =
            let tag = mat |> List.find_map (function
               | (Ph_tuple (tag,_),_loc),_ -> Some tag
               | (Ph_any,_loc), _ -> None)
            in
            match tag with
            | Some tag ->
               begin match List.partition (fun (t,_) -> Cons1.tuple_tag_equal t tag) cases with
               | (_::_::_), _ -> intfail "nonunique split cases"
               | [_, fields], rest ->
                  let Ex fields = Clist.of_list (List.rev fields) in
                  let this, others = split_on_case tag fields mat in
                  let cases, def = split rest others in
                  (tag, proj fields typs this)::cases, def
               | [], rest ->
                  (* This can happen when a pattern matches a case that the
                     type shows cannot occur *)
                  let _this, others = split_on_case tag [] mat in
                  split rest others
               end
            | None ->
               let def =
                 match cases with
                 | [] -> None
                 | cases ->
                    let dt = split_cases ~matchloc ~env typs (List.map snd mat) in
                    Some (List.map fst cases, dt)
               in
               [], def
          in
          let cases, def = split cases mat in
          Cases (cases, def)
     in
     let dt =
       match var with
       | Some v -> Bind (v, Hashcons.mk dt)
       | None -> dt
     in
     Hashcons.mk dt

let ptuple ~tag fields =
  Some (Ptuple (Some (Typedefs.Cons1.Tag.unparse tag), Exp.of_record_fields fields)),
  Location.noloc

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
  | _ :: len, Cases (cases, defaults) ->
     List.concat_map (fun (tag, fields) ->
       counterexamples_fields len fields
       |> List.map (fun (fs, ps) ->
         let fs = ptuple ~tag (List.rev fs) in
         Clist.(fs :: ps)))
       cases
     @
     match defaults with
     | Some (tags, dt) when not dt.total ->
        let case_pats : pat list =
          List.map (fun tag ->
            fixme; (* FIXME: make extensible, not closed *)
            ptuple ~tag [])
            tags
        in
        let head = List.fold_left pat_or (List.hd case_pats) (List.tl case_pats) in
        counterexamples len dt
        |> List.map (fun ps -> Clist.(head :: ps))
     | _ -> []

and counterexamples_fields :
  type n . (n,_) Clist.t -> n field_projections ->
               (pat Exp.field_list * (n, pat) Clist.t) list =
  fun len fs ->
  let mkfield fn a = ((fn, Location.noloc), Exp.map_exp_field (fun x -> Some x) a) in
  match fs with
  | Proj_end dt ->
     List.map (fun c -> [],c) (counterexamples len dt)
  | Proj_mand (fn, fs) ->
     let fs = counterexamples_fields (() :: len) fs in
     fs |> List.map (fun (fs, ((p :: ps) : (_ s, pat) Clist.t)) ->
       (mkfield fn (Mandatory p) :: fs), ps)
  | Proj_opt (fn, pres, abs) ->
     let pres =
       counterexamples_fields (() :: len) pres
       |> List.map (fun (fs, ((p :: ps) : (_ s, pat) Clist.t)) ->
         (mkfield fn (Optional p) :: fs), ps)
     in
     let abs =
       counterexamples_fields len abs
       |> List.map (fun (fs, ps) ->
         (mkfield fn Absent :: fs), ps)
     in
     pres @ abs

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
         Error.fail bloc (Illformed_pat (`Duplicate_name (`Var,k,aloc))))
      acc fvs
  in
  List.fold_left acc_pat SymMap.empty ps
and check_fvs = function
  | None, _ -> SymMap.empty
  | Some p, loc -> check_fvs' loc p
and check_fvs' ploc = function
  | Pany ->
     SymMap.empty
  | Pbind ((v, _), p) ->
     let p = check_fvs p in
     SymMap.add v ploc p
  | Ptuple (_, fs) ->
     Exp.record_fields ~loc:ploc fs
     |> List.filter_map (fun ((f, floc), pat) ->
        match pat with
        | Exp.Mandatory (Some p)
        | Exp.Optional (Some p) -> Some p
        | Exp.Mandatory None
        | Exp.Optional None ->
           Some (Some (pvar (Tuple_fields.string_of_field_name f, floc)), floc)
        | Exp.Absent | Exp.Abs_broken -> None)
     |> check_fvs_list
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
        bindings = None })
  in
  let Ex typs = Clist.of_list typs in
  let mat =
    List.map2 (fun (pps, _) b -> pps, b) cases actions
    |> List.concat_map (fun ((pps,loc), act) ->
      pps |> List.map (fun ps ->
        match Clist.of_list_length ~len:typs ps with
        | None -> Error.fail loc (Illformed_pat (`Wrong_length (List.length ps, Clist.length typs)))
        | Some ps -> ps, (SymMap.empty, act)))
  in
  let dtree = split_cases ~matchloc ~env typs mat in
  actions |> List.iter (fun act ->
    if act.bindings = None then
      Error.log ~loc:act.pat_loc Unused_pattern);
  begin match counterexamples (Clist.map ignore typs) dtree with
  | [] -> ()
  | unmatched ->
     Error.log ~loc:matchloc (Nonexhaustive (List.map Clist.to_list unmatched))
  end;
  actions, Ex (typs, dtree)

type compiled_action =
  | Act_unused
  | Act_unshared of IR.comp
  | Act_shared of IR.comp * (IR.cont IR.Binder.t * (string * IR.value IR.Binder.t) list)

let compile ~actions vals orig_dt =
  let rec compile :
     type w . vals:(w, IR.value) Clist.t -> w dectree -> IR.comp =
    fun ~vals dt -> compile_tree ~vals dt.tree
  and compile_tree :
     type w . vals:(w, IR.value) Clist.t -> w dectree' -> IR.comp =
    fun ~vals dt ->
    match dt, vals with
    | Done (bindings, act), [] ->
       begin match actions.(act.id) with
       | Act_unused -> assert false
       | Act_shared (_, (lbl, args)) ->
          Jump (IR.Binder.ref lbl,
                List.map (fun (v,_) -> IR.Var (SymMap.find v bindings)) args)
       | Act_unshared rhs ->
          rhs
       end
    | Failure, [] ->
       (* FIXME better error *)
       IR.Trap "match failure"
    | Any dt, _ :: vals ->
       compile ~vals dt
    | Bind (var, dt), (v :: _ as vals) ->
       LetVal (var, v, compile ~vals dt)
    (* Compile singleton pattern matches as projections *)
    | Cases ([(_tag, fs)], None), v :: vals ->
       Project (v, compile_fields ~vals fs)
    | Cases (cases, default), v :: vals ->
       let ir_sym_tag t = IR.Symbol.of_string (Cons1.Tag.to_ir_string t) in
       let cases =
         cases |> List.map (fun (tag, fs) ->
           let cont = compile_fields ~vals fs in
           ir_sym_tag tag, cont)
       in
       let default =
         default |> Option.map (fun (tags, dt) ->
           List.map ir_sym_tag tags,
           compile ~vals dt)
       in
       Match (v, cases, default)

  and compile_fields :
    type w . vals:(w, IR.value) Clist.t -> w field_projections -> IR.unpacking_cont =
    fun ~vals fs ->
    let vname : Tuple_fields.field_name -> string = function
      | Field_named s -> s
      | Field_positional n -> Printf.sprintf "v%d" n
    in
    match fs with
    | Proj_end dt ->
       [], compile ~vals dt
    | Proj_mand (fn, fs) ->
       let v = IR.Binder.fresh ~name:(vname fn) () in
       let binders, rest = compile_fields ~vals:(IR.var v :: vals) fs in
       (binders @ [fn,v]), rest
    | Proj_opt _ -> unimp "Proj_opt compilation"
  in
  let Ex (len, dt) = orig_dt in
  let vals = Option.get (Clist.of_list_length ~len vals) in
  let code = compile ~vals dt in
  List.fold_right
    (fun act acc ->
      match act with
      | Act_shared (rhs, (label, names)) ->
         IR.LetCont (label, List.map snd names, rhs, acc)
      | _ -> acc)
    (Array.to_list actions)
    code
