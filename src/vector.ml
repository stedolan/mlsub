type 'a t = {
  mutable contents : 'a array;
  mutable length : int;
}

let create () =
  { contents = [| |]; length = 0 }

let push v x =
  let pos = v.length in
  assert (pos <= Array.length v.contents);
  if pos = Array.length v.contents then begin
    let newlen =
      if v.length < 10 then 10 else v.length * 2 in
    let newcontents = Array.make newlen x in
    Array.blit v.contents 0 newcontents 0 v.length;
    v.contents <- newcontents;
    v.length <- newlen
  end else begin
    v.contents.(pos) <- x;
    v.length <- pos + 1;
  end;
  pos

let length { length; _ } = length
let get v i = v.contents.(i)

let iter v f =
  for i = 0 to v.length - 1 do
    f (v.contents.(i))
  done

let iteri v f =
  for i = 0 to v.length - 1 do
    f i (v.contents.(i))
  done