open Tuple_fields
open Typedefs



let loc : Exp.location =
 { source = "<none>";
   loc_start = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0};
   loc_end = {pos_fname="";pos_lnum=0;pos_cnum=0;pos_bol=0} }

let named_type s : Exp.tyexp' =
  Tnamed ({label=s; shift=0}, loc)

(* FIXME:
   this could generate simpler types by allowing some shadowing
   once we have Remy-style level markers, its easy to only bother
   freshenign against (an approx of) the names actually used *)
let freshen env names name =
  let pick_name n =
    match n, name with
    | 0, Some s -> s
    | n, Some s -> Printf.sprintf "%s_%d" s (n+1)
    | n, None when n < 26 ->
       String.make 1 (Char.chr (Char.code 'A' + n))
    | n, None -> Printf.sprintf "T_%d" (n-26) in
  let taken name =
    if SymMap.mem name names then true else
    match Check.env_lookup_type Simple env name with
    | _, _ -> true
    | exception _ -> false in
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

(* Should only be called on fully generalised types.
   In such types, all stypes are lone variables *)
let rec convert_styp' env pol (ty : Typedefs.styp) : Exp.tyexp' =
  wf_styp pol env ty;
  match ty with
  | Bound_var _ -> failwith "locally closed"
  | Cons { pol=_; cons } ->
     convert_cons convert_styp env pol cons
  | Free_vars { level=lvl; rest; vars=vs } ->
     assert (is_trivial pol rest);
     let v, () = Intlist.as_singleton vs in
     let name =
       match env_entry_at_level env lvl with
       | Erigid { vars; _ } ->
          vars.(v).name
       | Eflexible {vars=flexvars; _} ->
          (Vector.get flexvars v).name
       | _ -> assert false in
     match name with
     | None -> assert false
     | Some name -> named_type name
and convert_styp env pol ty =
  Some (convert_styp' env pol ty), loc

let rec convert env pol (ty : Typedefs.typ) : Exp.tyexp =
  wf_typ pol env ty;
  let tyexp : Exp.tyexp' = match ty with
    | Tcons t -> convert_cons convert env pol t
    | Tsimple sty -> convert_styp' env pol sty
    | Tpoly {names=_; bounds; flow; body} ->
       let names = ref SymMap.empty in
       let bounds = bounds |> Array.mapi (fun i (name,l,u) ->
         let name = freshen env !names name in
         names := SymMap.add name i !names;
         (name, (Some name, l, u))) in
       let vnames = Array.map fst bounds and bounds = Array.map snd bounds in
       let env, body = enter_poly pol env !names bounds flow body in
       wf_env env;
       let vars =
         match pol, env.entry with
         | Neg, Erigid { names=_; vars; flow=_ } ->
            vars |> Array.map (fun { name; rig_lower; rig_upper } ->
              name, (Neg, rig_lower), (Pos, rig_upper))
         | Pos, Eflexible {vars=flexvars; _} ->
            flexvars |> Vector.to_array |> Array.map (fun {name; pos; neg; _} ->
              (* drop flow *)
              let pos, _ = styp_unconsv env.level pos in
              let neg, _ = styp_unconsv env.level neg in
              name, (Pos, pos), (Neg, neg))
         | _ -> assert false in
       let constraints =
         vars |> Array.map (fun (name, (pl, l), (pu, u)) ->
           let name = match name with Some name -> name,loc | _ -> assert false in
           match (l = styp_bot pl), (u = styp_top pu) with
           | true, true -> [name, None]
           | false, true -> [name, Some (`Sup, convert_styp env pl l)]
           | true, false -> [name, Some (`Sub, convert_styp env pu u)]
           | false, false ->
              [name, Some (`Sub, convert_styp env pu u);
               name, Some (`Sup, convert_styp env pl l);])
         |> Array.to_list |> List.concat in
       let constraints =
         constraints @
           (Flow_graph.to_list flow |> List.map (fun (i,j) ->
             ((vnames.(i),loc), Some (`Sub, (Some (named_type vnames.(j)), loc))))) in
       Tforall (constraints, convert env pol body)
  in
  Some tyexp, loc
