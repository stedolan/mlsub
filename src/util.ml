exception Internal of string
let intfail fmt =
  Format.kasprintf (fun s -> raise (Internal s)) fmt
let () = Printexc.register_printer (function Internal s -> Some ("internal error: " ^ s) | _ -> None)

exception Unimplemented of string
let unimp fmt =
  Format.kasprintf (fun s -> raise (Unimplemented s)) fmt
let () = Printexc.register_printer (function Unimplemented s -> Some ("unimplemented: " ^ s) | _ -> None)

let id x = x

type zero = |
let never : zero -> 'a = function _ -> .

(* Immutable arrays *)
module IArray : sig
  type +'a t
  val empty : 'a t
  val make : 'a array -> 'a t
  val get : 'a t -> int -> 'a
  val length : 'a t -> int
  val of_list : 'a list -> 'a t
  val of_array : 'a array -> 'a t
  val to_list : 'a t -> 'a list
  val to_array : 'a t -> 'a array
  val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val iter : ('a -> unit) -> 'a t -> unit
  val iteri : (int -> 'a -> unit) -> 'a t -> unit
  val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val exists : ('a -> bool) -> 'a t -> bool
  val map_fold_left : ('s -> 'a -> 's * 'b) -> 's -> 'a t -> 's * 'b t
end = struct
  type +'a t = Mk : 'b array * ('b -> 'a) -> 'a t
  let acopy a = Array.map id a
  let empty = Mk ([| |], id)
  let make x = Mk (Array.map id x, id)
  let get (Mk (a, r)) i = r a.(i)
  let length (Mk (a, _r)) = Array.length a
  let of_list l = make (Array.of_list l)
  let of_array a = Mk(acopy a, id)
  let to_array (Mk (a, r)) = Array.map r a
  let to_list x = to_array x |> Array.to_list
  let map f (Mk (a, r)) = Mk (Array.init (Array.length a) (fun i -> f (r a.(i))), id)
  let mapi f (Mk (a, r)) = Mk (Array.init (Array.length a) (fun i -> f i (r a.(i))), id)
  let iteri f (Mk (a, ra)) =
    Array.iteri (fun i x -> f i (ra x)) a
  let iter2 f (Mk (a, ra)) (Mk (b, rb)) =
    Array.iter2 (fun a b -> f (ra a) (rb b)) a b
  let iter f (Mk (a, r)) = Array.iter (fun x -> f (r x)) a
  let exists f (Mk (a, r)) = Array.exists (fun x -> f (r x)) a
  let map_fold_left f s (Mk (a, r)) =
    let st = ref s in
    let out = ref [| |] in
    for i = 0 to Array.length a - 1 do
      let x = a.(i) in
      let s, b = f !st (r x) in
      let out =
        match !out with
        | [| |] -> out := Array.make (Array.length a) b; !out
        | o -> o in
      out.(i) <- b;
      st := s
    done;
    !st, of_array !out
end
type 'a iarray = 'a IArray.t


module UniqList : sig
  type +'a t = private 'a list
  module Make (El : sig type t val equal : t -> t -> bool end) : sig
    type el = El.t
    type nonrec t = el t

    val empty : t
    val single : el -> t
    val add : t -> el -> merge:(el -> el -> el) -> t
    val append : t -> t -> merge:(el -> el -> el) -> t
    val append' : t -> el list -> merge:(el -> el -> el) -> t
  
    val filter : t -> f:(el -> bool) -> t
    val partition : t -> f:(el -> bool) -> t * t
    val mem : el -> t -> bool
    val is_empty : t -> bool

    val pick : t -> el option

    (* equality as ordered lists *)
    val equal : ?eq:(el -> el -> bool) -> t -> t -> bool

    val iter : t -> f:(el -> unit) -> unit
    val to_list : t -> el list
    val of_list : merge:(el -> el -> el) -> el list -> t
  end
end = struct
  type 'a t = 'a list
  module Make (El : sig type t val equal : t -> t -> bool end) = struct
    type el = El.t
    type t = el list
  
    let empty = []
    let single x = [x]
  
    let rec add xs x ~merge =
      match xs with
      | [] -> [x]
      | x' :: xs ->
         if El.equal x x' then
           merge x' x :: xs
         else
           x' :: add xs x ~merge

    (* slow, but eh these are short lists *)
    let rec append xs ys ~merge =
      match ys with
      | [] -> xs
      | y :: ys -> append (add xs y ~merge) ys ~merge

    let append' = append
  
    let filter xs ~f = List.filter f xs

    let partition xs ~f = List.partition f xs
  
    let mem x xs = List.exists (El.equal x) xs

    let is_empty = function [] -> true | _ :: _ -> false

    let pick = function [] -> None | x :: _ -> Some x

    let equal ?(eq = El.equal) a b =
      try List.for_all2 eq a b
      with Invalid_argument _ -> false

    let iter xs ~f = List.iter f xs

    let to_list x = x

    let of_list ~merge x = append' ~merge empty x
  end
end

module Vector : sig
  type 'a t
  
  val create : unit -> 'a t
  
  val length : 'a t -> int
  val push : 'a t -> 'a -> int
  (* raises Invalid_argument if >= length *)
  val get : 'a t -> int -> 'a
  
  val to_array : 'a t -> 'a array
  val of_array : 'a array -> 'a t
  
  val clear : 'a t -> unit
  
  val iter : 'a t -> ('a -> unit) -> unit
  val iteri : 'a t -> (int -> 'a -> unit) -> unit
  
  val fold_lefti : ('a -> int -> 'b -> 'a) -> 'a -> 'b t -> 'a
end = struct
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
      let newcap =
        if v.length < 10 then 10 else v.length * 2 in
      let newcontents = Array.make newcap x in
      Array.blit v.contents 0 newcontents 0 v.length;
      v.contents <- newcontents;
      v.length <- pos + 1;
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
  
  let fold_lefti f acc vec =
    let r = ref acc in
    for i = 0 to vec.length - 1 do
      r := f !r i vec.contents.(i)
    done;
    !r
  
  let to_array vec = Array.sub vec.contents 0 vec.length
  let of_array arr = { contents = arr; length = Array.length arr }
  
  let clear vec = vec.length <- 0
end

module PPFmt = struct
  type group_opts =
    | No_opts
    | Junk of string
    | Nest of int

  type doc_stack =
    | Finished
    | Then_group of doc_stack * group_opts * PPrint.document

  type doc_state = doc_stack * PPrint.document

  let box_lit : _ CamlinternalFormat.acc -> string option = function
    | Acc_string_literal (End_of_acc, s)
       when String.length s > 2 && s.[0] = '<' && s.[String.length s - 1] = '>' ->
       Some (String.sub s 1 (String.length s - 2))
    | _ -> None

  open PPrint

  let parse_group_opts = function
    | None -> No_opts
    | Some s ->
       match int_of_string_opt s with
       | Some n -> Nest n
       | None -> No_opts

  let group_with_opts opts g =
    match opts with
    | No_opts -> group g
    | Junk s -> group (utf8string s ^^ g)
    | Nest n -> group (nest n g)

  (* Output a prefix of a format string, yielding a stack of documents *)
  let rec pp_acc (s : doc_state) (acc : _ CamlinternalFormat.acc) : doc_state =
    (* FIXME: what to do on bad nesting? *)
    match acc with
    (* Semantic tags ignored for now *)
    | Acc_formatting_gen (acc, Acc_open_tag _)
    | Acc_formatting_lit (acc, Close_tag) ->
       pp_acc s acc

    (* FIXME: use box info to decide group type *)
    | Acc_formatting_gen (acc, Acc_open_box tag) ->
       let st, curr = pp_acc s acc in
       Then_group (st, parse_group_opts (box_lit tag), curr), empty
    | Acc_formatting_lit (acc, Close_box) ->
       let st, curr = pp_acc s acc in
       begin match st with
       | Then_group (st, opts, pfx) ->
          st, pfx ^^ group_with_opts opts curr
       | Finished ->
          failwith "mismatched"
       end

    (* FIXME: honour offset? *)
    | Acc_formatting_lit(acc, Break(_, width, _offset)) ->
       let st, curr = pp_acc s acc in
       st, curr ^^ break width

    | Acc_formatting_lit(acc, (Force_newline | Flush_newline)) ->
       let st, curr = pp_acc s acc in
       st, curr ^^ hardline

    | Acc_formatting_lit(acc, Magic_size _) ->
       pp_acc s acc

    | Acc_formatting_lit(acc, Escaped_at) ->
       let st, curr = pp_acc s acc in
       st, curr ^^ char '@'

    | Acc_formatting_lit(acc, Escaped_percent) ->
       let st, curr = pp_acc s acc in
       st, curr ^^ char '%'

    (* FIXME: what is this? *)
    | Acc_formatting_lit(acc, Scan_indic c) ->
       let st, curr = pp_acc s acc in
       st, curr ^^ char '@' ^^ char c

    (* FIXME: how/what? *)
    | Acc_delay (acc, f) ->
       let st, curr = pp_acc s acc in
       let d = f () in
       st, curr ^^ d
(*
       let s = pp_acc s acc in
       f s*)

    (* 'Flushing' doesn't make much sense here, so ignore *)
    | Acc_formatting_lit (acc, FFlush)
    | Acc_flush acc ->
       pp_acc s acc

    | Acc_string_literal(acc, str)
    | Acc_data_string (acc, str) ->
       let st, curr = pp_acc s acc in
       st, curr ^^ utf8string str

    (* FIXME: Support Magic_size? *)
(*  | Acc_string_literal (Acc_formatting_lit (acc, Magic_size (_, size)), str)
    | Acc_data_string (Acc_formatting_lit (acc, Magic_size (_, size)), str) ->
       let st, curr = pp_acc s acc in
       asdf
    | Acc_char_literal (Acc_formatting_lit (acc, Magic_size (_, size)), ch)
    | Acc_data_char (Acc_formatting_lit (acc, Magic_size (_, size)), ch) ->
       let st, curr = pp_acc s acc in
       asdf *)

    | Acc_char_literal (acc, ch)
    | Acc_data_char (acc, ch) ->
       let st, curr = pp_acc s acc in
       st, curr ^^ char ch

    | Acc_invalid_arg (acc, msg) ->
       ignore (pp_acc s acc); invalid_arg msg

    | End_of_acc -> s

  let pp_acc acc =
    match pp_acc (Finished, empty) acc with
    | Finished, s -> s
    | _ -> failwith "mismatched"

  let kpp k (CamlinternalFormatBasics.Format (fmt, _)) =
    CamlinternalFormat.make_printf
      (fun acc -> k (pp_acc acc))
      End_of_acc fmt

  let pp fmt = kpp id fmt
end
