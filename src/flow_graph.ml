(* A directed graph represented as adjacency lists in both directions *)
type node = { pred : (int, unit) Intlist.t; succ : (int, unit) Intlist.t; }
type t = node array

(* FIXME: array + DFS might well be faster *)
let rec closure tbl vseen vnew =
  if Intlist.is_empty vnew then vseen
  else
    let vnext = Intlist.to_list vnew |> List.fold_left (fun t (v, ()) ->
      Intlist.union (fun _ () () -> ()) t (Intlist.remove tbl.(v).succ vseen)) Intlist.empty in
    closure tbl (Intlist.union (fun _ () () -> ()) vseen vnew) vnext

let reachable t i =
  closure t (Intlist.singleton i ()) t.(i).succ

let mem (t : t) i j =
  assert (0 <= i && i < Array.length t);
  assert (0 <= j && j < Array.length t);
  Intlist.contains t.(i).succ j
  || Intlist.contains (reachable t i) j

let make nodes =
  Array.mapi (fun i (pred, succ) ->
    Intlist.iter succ (fun j () ->
      assert (Intlist.contains (fst nodes.(j)) i));
    Intlist.iter pred (fun j () ->
      assert (Intlist.contains (snd nodes.(j)) i));
    { succ; pred }) nodes

let of_list len pairs =
  let nodes = Array.make len { succ = Intlist.empty; pred = Intlist.empty } in
  pairs |> List.iter (fun (i, j) ->
    nodes.(i) <- { nodes.(i) with succ = Intlist.add nodes.(i).succ j () };
    nodes.(j) <- { nodes.(j) with pred = Intlist.add nodes.(j).pred i () });
  nodes

let length t = Array.length t

let empty len =
  Array.init len (fun _ -> { succ = Intlist.empty; pred = Intlist.empty })

let fold f t s =
  t
  |> Array.mapi (fun i { succ; pred=_ } -> i, succ)
  |> Array.fold_left (fun s (i, succ) ->
     Intlist.to_list succ |> List.fold_left (fun s (j, ()) -> f s i j) s) s

let to_list (t : t) =
  fold (fun xs i j -> (i, j)::xs) t []
