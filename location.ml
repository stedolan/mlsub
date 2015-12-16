open Lexing
type source =
  { name : string;
    contents : string;
    (* (start, end) positions of lines, not including newline *)
    lines : (int * int) list }

type t = Loc of source * int * int

module type Locator = sig
  val pos : Lexing.position * Lexing.position -> t
end


let source name contents =
  let open Str in
  let rec lines p = function
    | [] -> []
    | [""] -> [] (* Files often end in a newline *)
    | s :: ss -> 
       let p' = p + String.length s in
       (p, p') :: lines (p' + 1) ss in
  { name; contents;
    lines = lines 0 (split_delim (regexp "\n") contents) }

let slurp chan =
  let rec read_all chunks =
    let buf = Bytes.init 4096 (fun _ -> '\x00') in
    match (input chan buf 0 (Bytes.length buf)) with
    | 0 -> Bytes.concat (Bytes.of_string "") (List.rev chunks)
    | n -> read_all (Bytes.sub buf 0 n :: chunks) in
  read_all []

let of_file fname =
  source fname (slurp (open_in fname))

let of_string str =
  source "<input>" str


let line_col (Loc (src, p, q)) =
  src.lines
  |> List.mapi (fun i (s, e) -> (i, s, e))
  |> List.filter (fun (i, s, e) -> p < e && s <= q)
  |> List.map (fun (i, s, e) ->
    (String.sub src.contents s (e - s),
     i,
     max 0 (p - s),
     min (e - s) (q - s)))

let loc_srcname (Loc (src, _, _)) = src.name

let print ppf loc =
  line_col loc
  |> List.iter (fun (txt, line, col_start, col_end) ->
    Format.fprintf ppf "%s:%d:%s\n%s:%d:%s%s\n" 
      (loc_srcname loc) (line + 1) txt
      (loc_srcname loc) (line + 1) (String.make col_start ' ') (String.make (col_end - col_start) '^'))


(*
let contains (Pos (s1, p, p')) (Pos (s2, q, q')) =
  s1 = s2 && p.pos_fname = q.pos_fname && p.pos_bol <= q.pos_bol && p'.pos_bol >= q'.pos_bol
*)

let internal =
  let loc = { name = "<internal>"; contents = "?"; lines = [(0,1)] } in
  Loc (loc, 0, 0)


type location = t
module LocSet = Set.Make (struct type t = location let compare = compare end)
type set = LocSet.t

let one = LocSet.singleton

let join = LocSet.union

let extract s = List.hd (LocSet.elements s)

let empty = LocSet.empty
