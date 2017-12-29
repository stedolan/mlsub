open Variance
open Typector
open Types
open Exp

module SMap = Symbol.Map

type scheme =
  { environment : state SMap.t;
    expr : state }

type dscheme =
  { d_environment : dstate SMap.t;
    d_expr : dstate }

type typing =
    scheme SMap.t -> scheme

let to_dscheme s =
  let states = s.expr :: SMap.fold (fun v s ss -> s :: ss) s.environment [] in
  let remap, dstates = Types.determinise states in
  let minim = Types.minimise dstates in
  let remap x = minim (remap x) in
  { d_environment = SMap.map remap s.environment; d_expr = remap s.expr }

let clone_scheme loc s =
  Types.clone (fun f -> { environment = SMap.map (f loc) s.d_environment; expr = f loc s.d_expr })

let constrain' loc err p n =
  let success = ref true in
  List.iter (fun e -> success := false; err e) (Types.constrain loc p n);
  !success

let dump_scheme ctx title {environment; expr} =
  Format.printf "%a\n%!" (print_automaton ctx title) (fun f ->
    f "out" expr;
    SMap.iter (fun n s -> f (Symbol.to_string n) s) environment)

let constrain loc ctx err name (inputs : (state * state) list) output =
  let dump title =
    let find_states f =
      let id = ref 0 in
      List.iter (fun (s, t) ->
                 f (Printf.sprintf "s-%d" !id) s;
                 f (Printf.sprintf "t-%d" !id) t;
                 incr id) inputs;
      f "out" output in
    Format.printf "%a\n%!" (print_automaton ctx title) find_states in
  let debug = false in
  if debug then dump (name ^ "_before");
  let errs = (List.fold_left (fun rs (p, n) -> rs @ constrain loc p n) [] inputs) in
  List.iter err errs;
  if debug then dump (name ^ "_after");
  match errs with
  | [] -> output
  | _ :: _ -> compile_type ctx Pos (TZero Pos)

let ty_join a b =
  let (jN, jP) = Types.flow_pair () in
  let errs =
    Types.constrain Location.internal a jN @
    Types.constrain Location.internal b jN in
  assert (errs = []);
  jP

let ty_join_neg a b =
  let (jN, jP) = Types.flow_pair () in
  let errs =
    Types.constrain Location.internal jP a @
    Types.constrain Location.internal jP b in
  assert (errs = []);
  jN

let join_scheme s s' =
  { expr = ty_join s.expr s'.expr;
    environment = SMap.merge (fun k t1 t2 ->
      match t1, t2 with
      | Some t1, Some t2 -> Some (ty_join_neg t1 t2)
      | x, None | None, x -> x) s.environment s'.environment }

let ascription ctx scheme typeterm =
  let s = compile_type ctx Pos typeterm in
  let top = compile_type ctx Neg (TZero Neg) in
  let dsch = to_dscheme { environment = SMap.map (fun _ -> top) scheme.environment; expr = s } in
  match subsumed (fun f -> f Pos scheme.expr dsch.d_expr &&
                             SMap.for_all (fun v sv ->
                               f Neg sv (SMap.find v dsch.d_environment)) scheme.environment) with
  | false -> failwith "ascription check failed"
  | true -> { environment = SMap.empty; expr = s }

let env_join err loc = SMap.merge (fun k a b -> match a, b with
  | (None, x) | (x, None) -> x
  | Some a, Some b ->
     Some (ty_join_neg a b))
(* Some (Types.join a b)) *)


let failure () =
  { environment = SMap.empty; expr = compile_type Typector.empty_context Pos (TZero Pos) }

let unused _ =
  compile_type Typector.empty_context Neg (TZero Neg)

let ctx0 =
  empty_context
  |> add_opaque_type () (Symbol.intern "int") []
  |> add_opaque_type () (Symbol.intern "unit") []
  |> add_opaque_type () (Symbol.intern "bool") []
  |> add_opaque_type () (Symbol.intern "string") []
  |> add_opaque_type () (Symbol.intern "list") [TParam (Some VPos, Symbol.intern "A")]


let (ty_int, ty_unit, ty_bool, ty_string) =
  let f s loc = Typector.ty_named' ctx0 (Symbol.intern s) [] loc in
  (f "int", f "unit", f "bool", f "string")

let ty_list t loc =
  Typector.ty_named' ctx0 (Symbol.intern "list") [APos (t loc)] loc




module IntMap = Map.Make (struct type t = int let compare = compare end)

type field_list = Symbol.t list (* sorted by hash order, no collisions *)


type case_code = { case_scheme : scheme ; mutable case_used : bool ; case_loc : Location.t }
type ('a, 'n) case_matrix = 
  ((Exp.pat, 'n) Vec.t * 'a) list

type ('a, 'n) pat_split =
  | PSNone
  | PSAny of ('a, 'n) case_matrix
  | PSInt of ('a, 'n) case_matrix IntMap.t * ('a, 'n) case_matrix
  | PSList of { ps_nil : ('a, 'n) case_matrix; ps_cons : ('a, 'n Vec.s Vec.s) case_matrix }
  | PSObj of ('a, 'n) field_split SMap.t * ('a, 'n) field_split option (* nonempty *)
and ('a, 'n) field_split =
  Fields : (Symbol.t, 'n, 'm) Vec.Prefix.t * ('a, 'm) case_matrix -> ('a, 'n) field_split

type 'a s = 'a Vec.s
type ('m,'r) expansion =
| Nil : ('m, 'm) expansion
| Item : ('m, 'r) expansion -> ('m s, 'r s) expansion
| Gap : ('m, 'r) expansion -> ('m, 'r s) expansion



type ('n, 'm1, 'm2) fields_merge =
| Merge : (Symbol.t, 'n, 'r) Vec.Prefix.t * ('m1, 'r) expansion * ('m2, 'r) expansion -> ('n, 'm1, 'm2) fields_merge

let rec mk_fields_merge :
  type n m1 m2 .
    (Symbol.t, n, m1) Vec.Prefix.t ->
    (Symbol.t, n, m2) Vec.Prefix.t ->
    (n, m1, m2) fields_merge =
  let open Vec.Prefix in
  fun pfs qfs -> match pfs, qfs with
  | [], [] -> Merge ([], Nil, Nil)
  | pf :: pfs', [] ->
     let Merge (fs, pexp, qexp) = mk_fields_merge pfs' [] in
     Merge (pf :: fs, Item pexp, Gap qexp)
  | [], qf :: qfs' ->
     let Merge (fs, pexp, qexp) = mk_fields_merge [] qfs' in
     Merge (qf :: fs, Gap pexp, Item qexp)
  | pf :: pfs', qf :: qfs' when Symbol.hash pf < Symbol.hash qf ->
     let Merge (fs, pexp, qexp) = mk_fields_merge pfs' qfs in
     Merge (pf :: fs, Item pexp, Gap qexp)
  | pf :: pfs', qf :: qfs' when Symbol.hash qf < Symbol.hash pf ->
     let Merge (fs, pexp, qexp) = mk_fields_merge pfs qfs' in
     Merge (qf :: fs, Gap pexp, Item qexp)
  | pf :: pfs', qf :: qfs' ->
     if pf <> qf then failwith "field hash collision";
     let Merge (fs, pexp, qexp) = mk_fields_merge pfs' qfs' in
     Merge (pf :: fs, Item pexp, Item qexp)

let dummy_pat : Exp.pat = (Location.internal, Some PWildcard)
let rec expand_fields :
  type m r .
       (m, r) expansion -> 
       (Exp.pat, m) Vec.t -> (Exp.pat, r) Vec.t =
  let open Vec in
  fun exp v -> match exp, v with
  | Nil, v -> v
  | Item exp, v :: vs -> v :: expand_fields exp vs
  | Gap exp, vs -> dummy_pat  :: expand_fields exp vs

let combine_fields (Fields (pfs, pm)) (Fields (qfs, qm)) =
  let Merge (fs, pexp, qexp) = mk_fields_merge pfs qfs in
  let expand_matrix m exp =
    m |> List.map (fun (pats, case) -> 
             expand_fields exp pats, case) in
  let pm' = expand_matrix pm pexp in
  let qm' = expand_matrix qm qexp in
  Fields (fs, pm' @ qm')

(* union of cases *)
let combine_splits (type n) (p : ('a, n) pat_split) (q : ('a, n) pat_split) : ('a, n) pat_split =
  let combine_ints (pis, pdef) (qis, qdef) =
    PSInt (IntMap.merge (fun i pi qi -> match pi, qi with
    | Some pi, Some qi -> Some (pi @ qi)
    | Some pi, None -> Some (pi @ qdef)
    | None, Some qi -> Some (pdef @ qi)
    | None, None -> None) pis qis, pdef @ qdef) in

  let combine_objs (ptags, pdef) (qtags, qdef) =
    PSObj (SMap.merge (fun tag ptag qtag -> match ptag, pdef, qtag, qdef with
           | Some pt, _, Some qt, _ -> Some (combine_fields pt qt)
           | Some pt, _, None, Some qdef -> Some (combine_fields pt qdef)
           | Some pt, _, None, None -> Some pt
           | None, Some pdef, Some qt, _ -> Some (combine_fields pdef qt)
           | None, None, Some qt, _ -> Some qt
           | None, _, None, _ -> None) ptags qtags,
           match pdef, qdef with
           | Some pdef, Some qdef -> Some (combine_fields pdef qdef)
           | x, None | None, x -> x) in

  match p, q with
  | PSNone, x | x, PSNone -> x

  | PSAny ps, PSAny qs -> PSAny (ps @ qs)

  | PSAny ps, PSInt (qis, qdef) ->
     combine_ints (IntMap.empty, ps) (qis, qdef)
  | PSInt (pis, pdef), PSAny qs ->
     combine_ints (pis, pdef) (IntMap.empty, qs)
  | PSInt (pis, pdef), PSInt (qis, qdef) ->
     combine_ints (pis, pdef) (qis, qdef)

  | PSAny ps, PSList { ps_nil; ps_cons } -> failwith "Unimplemented"
  | PSList { ps_nil; ps_cons }, PSAny ps -> failwith "Unimplemented"

  | PSList { ps_nil; ps_cons }, PSList { ps_nil = ps_nil'; ps_cons = ps_cons' } ->
     PSList { ps_nil = ps_nil @ ps_nil'; ps_cons = ps_cons @ ps_cons' }

  (* PSAny ps for objects is PSObj (SMap.empty, Some (ps, [])) *)
  | PSAny ps, PSObj (qtags, qdef) ->
     combine_objs (SMap.empty, Some (Fields (Vec.Prefix.[], ps))) (qtags, qdef)
  | PSObj (ptags, pdef), PSAny qs ->
     combine_objs (ptags, pdef) (SMap.empty, Some (Fields (Vec.Prefix.[], qs)))

  | PSObj (ptags, pdef), PSObj (qtags, qdef) ->
     combine_objs (ptags, pdef) (qtags, qdef)

  | PSInt _, (PSObj _ | PSList _)
  | PSObj _, (PSInt _ | PSList _)
  | PSList _, (PSObj _ | PSInt _) -> failwith "incompatible patterns"

let rec split_cases : type n . (Symbol.t -> 'a -> 'a) -> ('a, n s) case_matrix -> ('a, n) pat_split =
  let open Vec in
  fun bind cases -> match cases with
  | [] -> PSNone
  | ((loc, None) :: _, _) :: _ ->
     failwith "parse error?"
  | ((loc, Some p) :: ps, case) :: cases ->
     match p with
     | PWildcard ->
        combine_splits (PSAny [ps, case]) (split_cases bind cases)
     | PBind (v, p) ->
        split_cases bind ((p :: ps, bind v case) :: cases)
     | PObject (tag, unsorted_subpats) ->
        let open List in
        let sorted = List.sort (fun (t, p) (t', p') ->
          compare (Symbol.hash t) (Symbol.hash t')) unsorted_subpats in
        let rec to_fields = function
          | [] -> Fields(Vec.Prefix.[], [ps, case])
          | (f, p) :: rest ->
             (match rest with
              | (f', p') :: _ when Symbol.hash f = Symbol.hash f' ->
                 failwith "duplicate labels"
              | _ -> ());
             let Fields(fs, m) = to_fields rest in
             Fields(Vec.Prefix.(f :: fs), List.map (fun (ps, case) -> Vec.(p :: ps), case) m) in
        let fields = to_fields sorted in
        let split = match tag with
          | None -> PSObj (SMap.empty, Some fields)
          | Some t -> PSObj (SMap.singleton t fields, None) in
        combine_splits split (split_cases bind cases)
     | PInt n ->
        combine_splits (PSInt (IntMap.singleton n List.[ps, case], [])) (split_cases bind cases)
     | PNil ->
        combine_splits (PSList {ps_cons = []; ps_nil = [ps, case]}) (split_cases bind cases)
     | PCons (px, pxs) ->
        combine_splits (PSList {ps_cons = [px :: pxs :: ps, case]; ps_nil = []}) (split_cases bind cases)
     | PAlt (p1, p2) ->
        split_cases bind ((p1 :: ps, case) :: (p2 :: ps, case) :: cases)


let rec dump_decision_tree : type n . string -> ('a, n) case_matrix -> unit = fun pfx cases ->
  let open Vec in
  match cases with
  | [] -> Printf.printf "%s nonexhuastive!\n" pfx;
  | ([], _) :: rest ->
     Printf.printf "%s done\n" pfx;
  | ((_::_), _) :: _ as cases ->
     let split = split_cases (fun _ x -> x) cases in
     match split with
     | PSNone ->
        Printf.printf "%s nonexhaustive2\n" pfx;
     | PSAny cases ->
        Printf.printf "%s any\n" pfx;
        dump_decision_tree pfx cases
     | PSInt (ints, def) ->
        Printf.printf "%s ints:\n" pfx;
        ints |> IntMap.iter (fun i cases ->
          Printf.printf "%s %d:\n" pfx i;
          dump_decision_tree (pfx ^ "  ") cases);
        Printf.printf "%s _:\n" pfx;
        dump_decision_tree (pfx ^ "  ") def
     | PSList { ps_nil; ps_cons } ->
        Printf.printf "%s cons\n" pfx;
        dump_decision_tree (pfx ^ "  ") ps_cons;
        Printf.printf "%s nil\n" pfx;
        dump_decision_tree (pfx ^ "  ") ps_nil
     | PSObj (tags, def) ->
        Printf.printf "%s objs:\n" pfx;
        let p k fields =
          Printf.printf "%s %s [" pfx k;
          List.iter (Printf.printf "%s ") (List.map Symbol.to_string fields);
          Printf.printf "]\n" in
        tags |> SMap.iter (fun k (Fields (fields, cases)) ->
          p (Symbol.to_string k) (Vec.Prefix.to_list fields);
          dump_decision_tree (pfx ^ "  ") cases);
        match def with
        | Some (Fields (fields, cases)) ->
           p "_" (Vec.Prefix.to_list fields);
          dump_decision_tree (pfx ^ "  ") cases
        | None -> ()



type pat_desc =
  | PTAny
  | PTInt
  | PTList of pat_desc
  | PTObj of fields SMap.t * fields option
and fields = pat_desc SMap.t

(* IDEA: separate PTObj into two cases:
     PTObj of fields
     PTVar of fields SMap.t * fields option Lazy.t
   PTVar's default case is never opened, but may be used in merge_desc.
   pat_desc_to_type always ignores it *)


let mk_pat : rpat -> pat =
  fun p -> Location.internal, Some p

let rec rpat_is_empty = function
  | PWildcard
  | PInt _ -> false
  | PBind (v, pat) -> pat_is_empty pat
  | PNil -> false
  | PCons (px, pxs) -> pat_is_empty px || pat_is_empty pxs
  | PAlt (p1, p2) -> pat_is_empty p1 && pat_is_empty p2
  | PObject (_, fields) ->
     List.exists (fun (_, p) -> pat_is_empty p) fields
and pat_is_empty = function
  | _, Some p -> rpat_is_empty p
  | loc, None -> failwith "undefined pattern"

(* take the meet of two pat_descs,
   but with extra error checking
   (e.g. complain about int ⊓ { foo : int } rather than producing a meet type)
*)
let rec merge_desc s desc desc' =
  match desc, desc' with
  | PTAny, PTAny -> PTAny
  | PTAny, t' -> t'
  | t, PTAny -> t
  | PTInt, PTInt -> PTInt
  | PTInt, (PTObj _ | PTList _)
  | PTObj _, (PTInt | PTList _)
  | PTList _, (PTObj _ | PTInt) -> failwith "pattern type mismatch"
  | PTList e, PTList e' -> PTList (merge_desc (s ^ ", elem") e e')
  | PTObj (tags, def), PTObj (tags', def') ->
     let tags = SMap.merge (fun tag pat pat' ->
       match pat, def, pat', def' with
       | Some obj, _, Some obj', _ ->
          Some (merge_fields (s ^ ", tag: " ^ Symbol.to_string tag) obj obj')
       | None, Some def, Some obj, _
       | Some obj, _, None, Some def ->
          Some (merge_fields (s ^ ", dtag: " ^ Symbol.to_string tag) obj def)
       | None, None, Some obj, _
       | Some obj, _, None, None ->
          (* include this, but pick up on the nonex later *)
          Some obj
          (* failwith ("nonexhaustive because tag " ^ Symbol.to_string tag ^ " unmatched in " ^ s) *)
       | None, _, None, _ -> None) tags tags' in
     let def = (match def, def' with
       | d, None | None, d -> None
       | Some def, Some def' -> Some (merge_fields (s ^ ", def") def def')) in
     PTObj (tags, def)
and merge_fields s obj obj' =
  SMap.merge (fun field pat pat' -> match pat, pat' with
    | Some pat, Some pat' -> Some (merge_desc (s ^ ", field: " ^ Symbol.to_string field) pat pat')
    | p, None | None, p -> p) obj obj'



(* case matrices:
  [] = failure
  [([], e); ...] = success, handle e
  [(ps, e); ...] = more matching *)

type 'n match_desc = (pat_desc, 'n) Vec.t
let rec merge_match_descs :
  type n . string -> n match_desc -> n match_desc -> n match_desc = 
  fun s desc desc' ->
  let open Vec in
  match desc, desc' with
  | [], [] ->
     []
  | (p :: ps), (p' :: ps') ->
     let rs = merge_match_descs (s ^ "/") ps ps' in
     (merge_desc (s ^ ":") p p' :: rs)

let rec fields_of_pfx fdesc =
  List.fold_left (fun m (f, x) -> SMap.add f x m) SMap.empty (Vec.Prefix.to_list fdesc)

let rec infer_match_desc :
  type n . n Vec.num -> string -> (_, n) case_matrix -> n match_desc =
  fun width s cases ->
  let open Vec in
  match width with
  | Same -> []
  | Inc width' ->
     match split_cases (fun _ x -> x) cases with
     | PSNone ->
        repeat width PTAny
     | PSAny cases ->
        let rest = 
          infer_match_desc width' (s ^ "; _") cases in
        PTAny :: rest
     | PSInt (ints, def) ->
        let rest =
          let defdesc = infer_match_desc width' (s ^ "; i_") def in
          IntMap.fold (fun i cases desc ->
            let desc' = infer_match_desc width' (s ^ "; " ^ string_of_int i) cases in
            merge_match_descs s desc desc')
            ints defdesc in
        PTInt :: rest
     | PSList { ps_nil; ps_cons } ->
        let rest_nil =
          infer_match_desc width' (s ^ "; nil") ps_nil in
        let (ty_x :: ty_xs :: rest_cons) =
          infer_match_desc (Inc (Inc width')) (s ^ "; cons") ps_cons in
        let rest = merge_match_descs s rest_nil rest_cons in
        let list = merge_desc s (PTList ty_x) ty_xs in
        list :: rest
     | PSObj (tags, def) ->
        let add_len fs = Vec.add width' (Vec.Prefix.length fs) in
        let desc = match def with
          | Some (Fields (fs, m)) ->
             let tys = infer_match_desc (add_len fs) (s ^ "; def") m in
             let (fdesc, rest) = Vec.Prefix.zip fs tys in
             (PTObj (SMap.empty, Some (fields_of_pfx fdesc))) :: rest
          | None -> repeat (Inc width') PTAny (* FIXME correct? *) in
        SMap.fold (fun tag (Fields (fs, m)) desc ->
            let s = (s ^ "; '" ^ Symbol.to_string tag) in
            let tys = infer_match_desc (add_len fs) s m in
            let (fdesc, rest) = Vec.Prefix.zip fs tys in
            let desc' = (PTObj (SMap.singleton tag (fields_of_pfx fdesc), None)) :: rest in
            merge_match_descs s desc desc') tags desc

type 'n match_type = {
  columns : (Types.state, 'n) Vec.t;
  result : scheme;
  unhandled : (Exp.pat, 'n) Vec.t list
}

let join_match_types a b =
  { columns = Vec.zip a.columns b.columns |> Vec.map (fun (a, b) -> ty_join_neg a b);
    result = join_scheme a.result b.result;
    unhandled = a.unhandled @ b.unhandled }

let rec typecheck_match :
  type n . _ -> (pat_desc, n) Vec.t -> (_, n) case_matrix -> n match_type =
  fun err desc cases -> 
  let open Vec in
  match desc with
  | [] ->
    begin match cases with
    | [] ->
       (* nonexhaustive *)
       { columns = []; result = failure (); unhandled = [[]] }
    | ([], (bound, case)) :: _ ->
       case.case_used <- true;
       let env = SMap.fold (fun v tyP env ->
         match SMap.find v env with
         | tyN ->
            Types.constrain Location.internal tyP tyN |> List.iter err;
            SMap.remove v env
         | exception Not_found ->
            env) bound case.case_scheme.environment in
       { columns = []; 
         result = { case.case_scheme with environment = env }; 
         unhandled = [] }
    end
  | curr :: rest ->
     let cons_col ty pat mty = {
         columns = ty :: mty.columns;
         result = mty.result;
         unhandled = List.map (fun ps -> mk_pat pat :: ps) mty.unhandled
       } in
     let flow = ref (Types.zero Neg) in
     let bind v (bound, case) =
       if SMap.mem v bound then
         failwith ("Duplicate binding of " ^ Symbol.to_string v)
       else begin
         let (fN, fP) = Types.flow_pair () in
         flow := ty_join_neg !flow fN;
         SMap.add v fP bound, case
       end in
     let mty = match split_cases bind cases, curr with
     | PSNone, desc ->
        (* FIXME: should this constrain according to desc? *)
        cons_col (Types.zero Neg) PWildcard (typecheck_match err rest [])

     | PSAny cases, desc ->
        (* FIXME: should this constrain according to desc? *)
        cons_col (Types.zero Neg) PWildcard (typecheck_match err rest cases)

     | PSInt (ints, def), PTInt ->
        let def_mty = typecheck_match err rest def in
        let def_mty = cons_col (Types.cons Neg (ty_int Location.internal)) PWildcard def_mty in
        IntMap.fold (fun n mat acc ->
            let ty = typecheck_match err rest mat in
            join_match_types (cons_col (Types.cons Neg (ty_int Location.internal)) (PInt n) ty) acc) ints def_mty
     | PSInt _, _ -> Error.internal "Wrong match desc for PSInt"

     | PSList { ps_nil; ps_cons }, PTList desc_x ->
        let nil_mty = typecheck_match err rest ps_nil in
        let nil_mty = cons_col (Types.cons Neg (ty_list unused Location.internal)) PNil nil_mty in
        let cons_mty = typecheck_match err (desc_x :: curr :: rest) ps_cons in
        let cons_mty =
          let ty_x :: ty_xs :: columns' = cons_mty.columns in
          let ty = ty_join_neg ty_xs (Types.cons Neg (ty_list (fun _ -> ty_x) Location.internal)) in
          { columns = ty :: columns';
            result = cons_mty.result;
            unhandled = List.map (fun (m_x :: m_xs :: missing) ->
                            mk_pat (PCons (m_x, m_xs)) :: missing) cons_mty.unhandled } in
        join_match_types nil_mty cons_mty
     | PSList _, _ -> Error.internal "Wrong match desc for PSList"

     | PSObj (tags, def), PTObj (desc_tags, desc_def) ->
        let typecheck_fields tag fdesc (Fields (fs, m)) =
          let open Vec.Prefix in
          (* FIXME: finds are dodgy here *)
          let desc' = prepend (map (fun f -> SMap.find f fdesc) fs) rest in
          let mty = typecheck_match err desc' m in
          let fields, columns = zip fs mty.columns in
          let to_smap f = f 
            |> to_list
            |> List.fold_left (fun m (f, x) -> SMap.add f (fun _ -> x) m) SMap.empty in
          let ty = match tag with
            | None ->
               ty_obj_cases
                 (SMap.map (fun fs -> SMap.empty) desc_tags)
                 (Some (to_smap fields))
            | Some tag ->
               ty_obj_cases
                 (SMap.add tag (to_smap fields) (SMap.map (fun fs -> SMap.empty) desc_tags))
                 None in
          { columns = Types.cons Neg (ty Location.internal) :: columns;
            result = mty.result;
            unhandled = List.map (fun missing ->
                            let (missing_fs, missing_rest) = zip fs missing in
                            Vec.(mk_pat (PObject (tag, Prefix.to_list missing_fs)) ::
                                   missing_rest)) mty.unhandled } in
        if SMap.is_empty desc_tags then
          (* FIXME split up psobj *)
          let (Some fdesc, Some fs) = desc_def, def in
          typecheck_fields None fdesc fs
        else
          (* ignore def for now *)
          let join_match_types' a b =
            match b with None -> Some a | Some b -> Some (join_match_types a b) in
          let Some mty = SMap.fold (fun tag fdesc acc ->
              let tag_fields =
                match SMap.find tag tags with
                | fs -> Some fs
                | exception Not_found -> None in
              let fields = match tag_fields, def with
                | Some fs, _ -> Some fs
                | None, Some fs -> Some fs
                | None, None -> None in
              match fields with
              | Some fs ->
                 join_match_types' (typecheck_fields (Some tag) fdesc fs) acc
              | None ->
                 (* FIXME: should probably constrain by desc *)
                 let mty = typecheck_match err rest [] in
                 join_match_types' (cons_col (Types.cons Neg (ty_obj_cases (SMap.add tag SMap.empty (SMap.map (fun fs -> SMap.empty) desc_tags)) None Location.internal))
                                             (PObject (Some tag, [])) mty)
                                   acc)
              desc_tags None in
          mty
     | PSObj _, _ -> Error.internal "Wrong match desc for PSObj" in
     let (curr :: rest) = mty.columns in
     { mty with columns = ty_join_neg !flow curr :: rest }


let rec variables_bound_in_pat err : pat list -> Location.t SMap.t = function
  | [] -> SMap.empty
  | (l, None) :: ps -> variables_bound_in_pat err ps
  | (l, Some p) :: ps ->
     match p with
     | PWildcard ->
        variables_bound_in_pat err ps
     | PBind (v, p) ->
        let vs = variables_bound_in_pat err (p :: ps) in
        (match SMap.find v vs with
        | l' -> err (Error.Rebound (`Value, l, v, l')); vs
        | exception Not_found -> SMap.add v l vs)
     | PObject (_, fs) ->
        variables_bound_in_pat err (List.map snd fs @ ps)
     | PInt n ->
        variables_bound_in_pat err ps
     | PNil ->
        variables_bound_in_pat err ps
     | PCons (px, pxs) ->
        variables_bound_in_pat err (px :: pxs :: ps)
     | PAlt (p1, p2) ->
        let v1 = variables_bound_in_pat err (p1 :: ps) in
        let v2 = variables_bound_in_pat err (p2 :: ps) in
        SMap.merge (fun k v1 v2 -> match v1, v2 with
        | Some l, Some l' ->
           Some l
        | (Some l, None) | (None, Some l) ->
           err (Error.Partially_bound (`Value, l, k));
           Some l
        | None, None ->
           None) v1 v2



let add_singleton v gamma loc =
  let (n, p) = Types.flow_pair () in
  let singleton = {
    environment = SMap.singleton v n;
    expr = p} in
  SMap.add v (to_dscheme singleton) gamma


open Exp
let var env arg t = try [t, SMap.find arg env] with Not_found -> []








let rec typecheck ctx err gamma = function
| (loc, Some exp) -> typecheck' ctx err gamma loc exp
| (loc, None) ->
   (* syntax error already logged by parser *)
   failure ()
and typecheck' ctx err gamma loc exp = match exp with
  | Var v ->
     (try clone_scheme (Location.one loc) (SMap.find v gamma)
      with Not_found -> (err (Error.Unbound (`Value, loc, v)); failure ()))

  | Lambda (params, body) ->
     let rec check_params gamma = function
       (* FIXME check for duplicate arguments *)
       (* FIXME check type parameters and type annotations *)
       | [] -> typecheck ctx err gamma body
       | (loc, (((Ppositional arg | Preq_keyword arg | Popt_keyword(arg, _)) as param), asc)) :: params ->
          let gamma = match asc with
            | Some t ->
               let (n, p) = Types.compile_type_pair ctx t in
               SMap.add arg (to_dscheme {
                 environment = SMap.singleton arg n;
                 expr = p}) gamma
            | None -> add_singleton arg gamma loc in
          let body_ty = check_params gamma params in
          let env = match param with
            | Popt_keyword (arg, default) ->
               let {environment = envD; expr = exprD} = typecheck ctx err gamma default in
               let (defaultN, defaultP) = Types.flow_pair () in
               let _ = constrain' loc err exprD defaultN in
               (match SMap.find arg body_ty.environment with
                | t -> let _ = constrain' loc err defaultP t in ()
                | exception Not_found -> ());
               env_join err loc envD body_ty.environment
            | _ -> body_ty.environment in
          { environment = env; expr = body_ty.expr } in

     let rec build_funtype env expr pos kwargs = function
       | [] -> { environment = env;
                 expr = Types.cons Pos (ty_fun (List.rev pos) kwargs expr loc) }
       | (loc, (((Ppositional arg | Preq_keyword arg | Popt_keyword (arg, _)) as param), _)) :: params ->
          let argty = try SMap.find arg env with Not_found -> Types.zero Neg in
          let env = SMap.remove arg env in
          let argty = fun _ -> argty in (* FIXME *)
          match param with
          | Ppositional _ ->
             build_funtype env expr (argty :: pos) kwargs params
          | Preq_keyword arg ->
             build_funtype env expr pos (Typector.SMap.add arg (argty, true) kwargs) params
          | Popt_keyword (arg, _) ->
             build_funtype env expr pos (Typector.SMap.add arg (argty, false) kwargs) params in

     let { environment; expr } = check_params gamma params in
     build_funtype environment (fun _ -> expr) [] (Typector.SMap.empty) params
(*
     let body_ty = check_params gamma params in
     let argvar k = ty_var ("arg-" ^ Symbol.to_string k) in
     let rec remove_params env = function
       | [] -> [], env
       | (loc, ((Ppositional arg | Preq_keyword arg | Popt_keyword (arg, _)), ty)) :: params ->
          let (constraints, env) = remove_params env params in
          let constraints = match ty with
            | None -> constraints
            | Some ty ->
               (* FIXME default arg unchecked here *)
               match SMap.find arg env with
               | v -> Printf.printf "constraining\n%!"; (v, ty) :: constraints
               | exception Not_found -> constraints in
          (var env arg (argvar arg loc) @ constraints), SMap.remove arg env in
     let rec build_funtype pos kwargs = function
       | [] -> ty_fun (List.rev pos) kwargs (ty_var "res") loc
       | (loc, (Ppositional arg, _)) :: params ->
          build_funtype (argvar arg :: pos) kwargs params
       | (loc, (Preq_keyword arg, _)) :: params ->
          build_funtype pos (Typector.SMap.add arg (argvar arg, true) kwargs) params
       | (loc, (Popt_keyword (arg, _), _)) :: params ->
          build_funtype pos (Typector.SMap.add arg (argvar arg, false) kwargs) params in
     let (constraints, env) = remove_params body_ty.environment params in
     { environment = env;
       expr = constrain err "lambda" ((body_ty.expr, ty_var "res" loc) :: constraints) Pos (TCons (build_funtype [] Typector.SMap.empty params)) }
*)
  | Let (name, exp, body) ->
     let exp_ty = typecheck ctx err gamma exp in
     let body_ty = typecheck ctx err (SMap.add name (to_dscheme exp_ty) gamma) body in
     (* CBV soundness: use exp_ty even if name is unused *)
     { environment = env_join err loc exp_ty.environment body_ty.environment;
       expr = body_ty.expr }

  | Rec (v, exp) ->
     let exp_ty = typecheck ctx err (add_singleton v gamma loc) exp in
     let (recN, recP) = Types.flow_pair () in
     let var = try [recP, SMap.find v exp_ty.environment] with Not_found -> [] in
     { environment = SMap.remove v exp_ty.environment;
       expr = constrain loc ctx err "rec" ((exp_ty.expr, recN) :: var) recP }

  | App (fn, args) ->
     let { environment = envF; expr = exprF } = typecheck ctx err gamma fn in
     let rec check_args env pos kwargs constraints = function
       | [] ->
          let (resN, resP) = Types.flow_pair () in
          { environment = env;
            expr = constrain loc ctx err "app"
              ((exprF, Types.cons Neg (ty_fun (List.rev pos) kwargs (fun _ -> resN) loc))
               :: constraints)
              resP }
       | (loc, Apositional e) :: args ->
          let { environment = envE; expr = exprE } = typecheck ctx err gamma e in
          let (argN, argP) = Types.flow_pair () in
          check_args (env_join err loc env envE) ((fun _ -> argP) :: pos) kwargs ((exprE, argN) :: constraints) args
       | (loc, Akeyword (k, e)) :: args ->
          let { environment = envE; expr = exprE } = typecheck ctx err gamma e in
          let (argN, argP) = Types.flow_pair () in
          check_args (env_join err loc env envE) pos (Typector.SMap.add k ((fun _ -> argP), true) kwargs) ((exprE, argN) :: constraints) args in
     check_args envF [] Typector.SMap.empty [] args

  | Seq (e1, e2) ->
     let {environment = env1; expr = expr1 } = typecheck ctx err gamma e1 in
     let {environment = env2; expr = expr2 } = typecheck ctx err gamma e2 in
     let (expN, expP) = Types.flow_pair () in
     { environment = env_join err loc env1 env2;
       expr = constrain loc ctx err "seq" [(expr1, Types.cons Neg (ty_unit loc)); (expr2, expN)] expP }

  | Typed (e, ty) ->
     let {environment; expr} = typecheck ctx err gamma e in
     let (n, p) = Types.compile_type_pair ctx ty in
     { environment; expr = constrain loc ctx err "typed" [expr, n] p }

  | Unit ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_unit loc) }

  | Int n ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_int loc) }

  | String s ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_string loc) }

  | Bool b ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_bool loc) }

  | If (cond, tcase, fcase) ->
     let {environment = envC; expr = exprC} = typecheck ctx err gamma cond in
     let {environment = envT; expr = exprT} = typecheck ctx err gamma tcase in
     let {environment = envF; expr = exprF} = typecheck ctx err gamma fcase in
     { environment = env_join err loc envC (env_join err loc envT envF);
       expr = constrain loc ctx err "if" [exprC, Types.cons Neg (ty_bool loc)]
         (ty_join exprT exprF) }
  | Nil ->
     { environment = SMap.empty; expr = Types.cons Pos (ty_list (fun _ -> Types.zero Pos) loc) }
  | Cons (x, xs) ->
     let x_ty = typecheck ctx err gamma x in
     let xs_ty = typecheck ctx err gamma xs in
     let (xN, xP) = Types.flow_pair () and (xsN, xsP) = Types.flow_pair () in
     { environment = env_join err loc x_ty.environment xs_ty.environment;
       expr = constrain loc ctx err "cons" [x_ty.expr, xN;
                                xs_ty.expr, Types.cons Neg (ty_list (fun _ -> xsN) loc)] (Types.cons Pos (ty_list (fun _ -> ty_join xP xsP) loc)) }

  | Match (scr, []) ->
     Error.internal "empty match unsupported"
  | Match (scr, ((((_, ps), e) :: _) as cases)) ->
     let scr_schemes = List.map (typecheck ctx err gamma) scr in
     let scr_env = List.fold_left (fun e s -> env_join err loc e s.environment) SMap.empty scr_schemes in
     let Vec.Vecn ps_v0 = Vec.of_list ps in
     let npats = Vec.length ps_v0 in
     let cases = cases |> List.map (fun ((loc, pats), e) ->
       let bound = variables_bound_in_pat err pats in
       let gamma =
         bound |> SMap.bindings |> List.map fst |>
             List.fold_left (fun gamma var -> add_singleton var gamma loc) gamma in
       let sch = typecheck ctx err gamma e in
       let case = { case_scheme = sch; case_loc = loc; case_used = false } in
       match Vec.(as_length npats (Vec.of_list pats)) with
       | None -> failwith "wrong lengths"
       | Some pats -> pats, (SMap.empty, case)) in
     (* dump_decision_tree "" cases; *)
     Printf.printf "%!";
     let desc = infer_match_desc npats "" cases in
     let mty = typecheck_match err desc cases in
     cases |> List.iter (fun (_, (_, { case_loc; case_used })) ->
       if not case_used then err (Error.Unused_case case_loc));
     begin match mty.unhandled with
     | [] -> ()
     | u -> err (Error.Nonexhaustive_match (loc, List.map Vec.to_list u))
     end;
     let rec bind_pats scrs pats = match scrs, pats with
       | [], [] -> ()
       | [], _ -> failwith "too many patterns"
       | _, [] -> failwith "not enough patterns"
       | scr :: scrs, pat :: pats ->
          Types.constrain loc scr.expr pat
          |> List.iter err;
          bind_pats scrs pats in
     bind_pats scr_schemes (Vec.to_list mty.columns);
     { expr = mty.result.expr; environment = env_join err loc scr_env mty.result.environment }

  | Object (tag, o) ->
     let (env, fields) = List.fold_right (fun (s, e) (env, fields) ->
        let {environment = env'; expr = expr'} = typecheck ctx err gamma e in
        if Typector.SMap.mem s fields then failwith "Duplicate field";
        (env_join err loc env env', Typector.SMap.add s (fun _ -> expr') fields)) o (SMap.empty, Typector.SMap.empty) in
     { environment = env; expr = Types.cons Pos (ty_obj_tag tag fields loc) }

  | GetField (e, field) ->
     let e_ty = typecheck ctx err gamma e in
     let (xN, xP) = Types.flow_pair () in
     { environment = e_ty.environment;
       expr = constrain loc ctx err "field" [e_ty.expr,
                                     Types.cons Neg (ty_obj (Typector.SMap.singleton field (fun _ -> xN)) loc)]
                        xP }






let ty_cons t loc = TCons (t loc)
let ty_fun2 x y res = ty_fun [x; y] Typector.SMap.empty res

let ty_polycmp = ty_fun2 (fun _ -> TZero Neg) (fun _ -> TZero Neg) (ty_cons (ty_bool))
let ty_binarith = ty_fun2 (ty_cons ty_int) (ty_cons ty_int) (ty_cons ty_int)

let predefined =
  ["p", ty_fun [ty_cons ty_int] Typector.SMap.empty (ty_cons ty_unit);
   "error", ty_fun [ty_cons ty_unit] Typector.SMap.empty (fun loc -> TZero Pos);
   "(==)", ty_polycmp;
   "(<)", ty_polycmp;
   "(>)", ty_polycmp;
   "(<=)", ty_polycmp;
   "(>=)", ty_polycmp;
   "(+)", ty_binarith;
   "(-)", ty_binarith]
  |> List.map (fun (n, t) -> (n, ty_cons t Location.internal))

let gamma0 =
  List.fold_right
    (fun (n, t) g ->
     SMap.add (Symbol.intern n)
              (to_dscheme { environment = SMap.empty;
                            expr = compile_type ctx0 Pos t }) g)
    predefined SMap.empty

type result =
  | Type of scheme
  | TypeError of string


type 'a sigitem =
  | SDef of Symbol.t * 'a
  | SLet of Symbol.t * 'a
and signature = Typector.context * dstate sigitem list

let rec infer_module err modl : signature =
  let rec infer tyctx gamma = function
    | [] -> tyctx, SMap.empty, []
    | (loc, MType (t, p, body)) :: modl ->
       (* Type definition *)
       infer (add_type_alias err t p body tyctx) gamma modl
    | (loc, MOpaqueType (t, p)) :: modl ->
       infer (add_opaque_type err t p tyctx) gamma modl
    | (loc, MDef (f, p, body)) :: modl ->
       (* Possibly-recursive function *)
       let {environment = envF; expr = exprF} as tyF =
         typecheck' tyctx err gamma loc (Rec (f, (loc, Some (Lambda (p, body))))) in
       let ctxM, envM, sigM = infer tyctx (SMap.add f (to_dscheme tyF) gamma) modl in
       ctxM, env_join err loc envF envM, (SDef (f, exprF) :: sigM)
    | (loc, MLet (v, e)) :: modl ->
       let {environment = envE; expr = exprE} = typecheck tyctx err gamma e in
       let ctxM, envM, sigM = infer tyctx (add_singleton v gamma loc) modl in
       ctxM, env_join err loc envE (SMap.remove v envM),
       let (expN, expP) = Types.flow_pair () in
       (SLet (v, constrain loc tyctx err "let" ((exprE, expN) :: var envM v expP)
         expP) :: sigM) in
  let ctxM, envM, sigM = infer ctx0 gamma0 modl in
  assert (SMap.is_empty envM);
  let states = List.map (function SDef (f, t) -> t | SLet (v, t) -> t) sigM in
  let remap, dstates = Types.determinise states in
  Types.optimise_flow dstates;
  let minim = Types.minimise dstates in
  ctxM, List.map (function SDef (f, t) -> SDef (f, minim (remap t)) | SLet (v, t) -> SLet (v, minim (remap t))) sigM

let rec print_signature ppf ((ctx, sigm) : signature) =
  let elems = sigm
     |> Types.clone (fun f -> List.map (function SLet (_, t) | SDef (_, t) -> f (Location.one Location.internal) t))
     |> decompile_automaton in
  let print s t = match s with
    | SLet (v, _) ->
       Format.fprintf ppf "val %s : %a\n%!" (Symbol.to_string v) (Printers.pp_typeterm ctx) t
    | SDef (f, _) ->
       Format.fprintf ppf "def %s : %a\n%!" (Symbol.to_string f) (Printers.pp_typeterm ctx) t in
  List.iter2 print sigm elems
