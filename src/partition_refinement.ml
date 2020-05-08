type set = {
  mutable ix : int;
  mutable split : set;
}
let rec dummy = {ix = -1; split = dummy}

type t = {
  nelems : int;
  set_of : set array;
} 

let make n =
  let s = { ix = -1; split = dummy } in
  { nelems = n;
    set_of = Array.make n s }

let refine p xs =
  let xs = ref xs in
  let split_sets = ref [] in
  while !xs <> [] do
    let x = List.hd !xs in
    xs := List.tl !xs;
    let s = p.set_of.(x) in
    if s.split == dummy then begin
      s.split <- { ix = -1; split = dummy };
      split_sets := s :: !split_sets;
    end;
    p.set_of.(x) <- s.split
  done;
  while !split_sets <> [] do
    (List.hd !split_sets).split <- dummy;
    split_sets := List.tl !split_sets;
  done

let to_sets p =
  let ix = ref 0 in
  for i = 0 to p.nelems - 1 do
    let s = p.set_of.(i) in
    if s.ix = -1 then begin
      s.ix <- !ix;
      incr ix
    end
  done;
  let elems = Array.make !ix [] in
  for i = p.nelems - 1 downto 0 do 
    let s = p.set_of.(i) in
    elems.(s.ix) <- i :: elems.(s.ix)
  done;
  for i = 0 to p.nelems - 1 do
    p.set_of.(i).ix <- -1
  done;
  Array.to_list elems
