open Tuple_fields
open Typedefs


type name_env_entry = string array

type nenv = name_env_entry gen_env

let loc : Exp.location =
 { source = "<none>";
   loc_start = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0};
   loc_end = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0} }

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, loc)

(* FIXME hilariously slow *)
let rec contains_name s (env : nenv) =
  match env with
  | Env_nil -> false
  | Env_cons { entry; rest; level=_ } ->
     if Array.mem s entry then true
     else contains_name s rest

(* FIXME:
   this could generate simpler types by allowing some shadowing
   once we have Remy-style level markers, its easy to only bother
   freshenign against (an approx of) the names actually used *)
let freshen (env : nenv) names name =
  let pick_name n =
    match n, name with
    | 0, Some s -> s
    | n, Some s -> Printf.sprintf "%s_%d" s (n+1)
    | n, None when n < 26 ->
       String.make 1 (Char.chr (Char.code 'A' + n))
    | n, None -> Printf.sprintf "T_%d" (n-26) in
  let taken name =
    if SymMap.mem name names then true else
    if contains_name name env then true else
    if lookup_named_type name <> None then true else
    false in
  let rec go n =
    let name = pick_name n in
    if not (taken name) then name else go (n+1) in
  go 0

let convert_cons conv env pol (ty : _ Typedefs.cons_head) =
  match ty with
  | Top -> named_type "any"
  | Bot -> named_type "nothing"
  | Bool -> named_type "bool"
  | Int -> named_type "int"
  | String -> named_type "string"
  | (Record fs) ->
       Trecord (Tuple_fields.map_fields (fun _ t -> conv env pol t) fs)
  | (Func (args, ret)) ->
       Tfunc (Tuple_fields.map_fields (fun _ t -> conv env (polneg pol) t) args,
              conv env pol ret)

let wf_vars_named _pol names vs =
  Intlist.iter vs (fun v () -> assert (0 <= v && v < Array.length names))

(* Should only be called on fully generalised types.
   In such types, all stypes are lone variables *)
let rec convert_styp' (env : nenv) pol (ty : Typedefs.styp) : Exp.tyexp' =
  wf_styp_gen wf_vars_named pol env ty;
  match ty with
  | Bound_var _ -> failwith "locally closed"
  | Cons { pol=_; cons } ->
     convert_cons convert_styp env pol cons
  | Free_vars { level=lvl; rest; vars=vs } ->
     assert (is_trivial pol rest);
     let v, () = Intlist.as_singleton vs in
     named_type (env_entry_at_level env lvl).(v)
and convert_styp env pol ty =
  Some (convert_styp' env pol ty), loc

let enter_poly_for_convert env pol bounds flow =
  let names = ref SymMap.empty in
  let bounds = bounds |> Array.mapi (fun i (name,l,u) ->
    let name = freshen env !names name in
    names := SymMap.add name i !names;
    (name, (l, u))) in
  let vnames = Array.map fst bounds in
  let sort = match pol with Pos -> Esort_flexible | Neg -> Esort_rigid in
  let level = env_next_level env sort in
  let env = Env_cons {level; entry=vnames; rest=env} in
  let inst pol v =
    styp_vars pol level (Intlist.singleton v ()) in
  let pl = pol and pu = polneg pol in
  let bound_constraints = bounds |> Array.map (fun (name, (l, u)) ->
    let name = name, loc in
    let l = map_bound_styp 0 inst pl l in
    let u = map_bound_styp 0 inst pu u in
    match (l = styp_bot pl), (u = styp_top pu) with
    | true, true -> [name, None]
    | false, true -> [name, Some (`Sup, convert_styp env pl l)]
    | true, false -> [name, Some (`Sub, convert_styp env pu u)]
    | false, false ->
       [name, Some (`Sub, convert_styp env pu u);
        name, Some (`Sup, convert_styp env pl l)])
    |> Array.to_list |> List.concat in
  let flow_constraints =
    Flow_graph.to_list flow |> List.map (fun (i,j) ->
      (vnames.(i),loc), Some (`Sub, (Some (named_type vnames.(j)), loc))) in
  env, (bound_constraints @ flow_constraints), inst


let rec convert (env : nenv) pol (ty : Typedefs.typ) : Exp.tyexp =
  (* wf_typ pol env ty; *)
  let tyexp : Exp.tyexp' = match ty with
    | Tcons t -> convert_cons convert env pol t
    | Tsimple sty -> convert_styp' env pol sty
    | Tpoly {names=_; bounds; flow; body} ->
       let env, constraints, inst = enter_poly_for_convert env pol bounds flow in
       let body = map_bound_typ 0 inst pol body in
       Tforall (constraints, convert env pol body)
  in
  Some tyexp, loc
