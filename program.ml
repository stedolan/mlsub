module Symbol = struct
  let sym_table = Hashtbl.create 20
  let id_table = Hashtbl.create 20
    
  type t = int

  let next_id = ref 0
  let fresh () = let x = !next_id in (incr next_id; x)

  let intern (s : string) : t = 
    try Hashtbl.find sym_table s
    with Not_found -> 
      let n = fresh () in
      Hashtbl.add sym_table s n;
      Hashtbl.add id_table n s;
      n
        
  let to_string (n : t) : string = Hashtbl.find id_table n

end

open Types

module SMap = Map.Make (struct type t = int let compare = compare end)

type scheme = 
  { environment : state SMap.t;
    expr : state }

let constrain (inputs : (state * var typeterm) list) p output =
  let (inputs, output) = compile_terms (fun f ->
    (List.map (fun (s, t) -> (s, f (polneg s.Types.State.pol) t)) inputs, f p output)) in
  if not (List.fold_left (fun b (s, c) -> b && 
    match s.Types.State.pol with
    | Pos -> assert (c.Types.State.pol = Neg); contraction s c
    | Neg -> assert (c.Types.State.pol = Pos); contraction c s) true inputs)
  then failwith "type error of some sort";
  output

(*
let constrain (schemes : scheme list) (constraints : tyconstraint) : scheme =
  assert (List.length schemes = List.length constraints.inputs);
  let environment = List.fold_left (fun env s -> Intmap.union_with (fun s s' -> merge s s'; s) env s.environment)
    (List.hd schemes).environment (List.tl schemes) in
  if not (List.fold_left2 (fun b s c -> b && contraction s.expr c) true schemes constraints.inputs)
  then failwith "type error of some sort";
  { environment; expr = constraints.output }
*)
