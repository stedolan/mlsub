open Lexing
type source =
  { name : string;
    contents : string;
    (* (start, end) positions of lines, including newline *)
    lines : (int * int) list }

type t = Loc of source * int * int

module type Locator = sig
  val pos : Lexing.position * Lexing.position -> t
end

(* Split a string by a delimiter. Delimiters are included in the result,
   so concatenating the output gives the original string *)
let rec split_term r s =
  let open Str in
  let item ss = ss |> List.rev |> String.concat "" in
  let rec join res acc = function
    | [] -> List.rev
       (match acc with
       | [] -> res | _ -> item acc :: res)
    | Text s :: rest ->
       join res (s :: acc) rest
    | Delim s :: rest ->
       join (item (s :: acc) :: res) [] rest in
  join [] [] (full_split r s)

let source name contents =
  let rec lines p = function
    | [] -> []
    | s :: ss -> 
       let p' = p + String.length s in
       (p, p') :: lines p' ss in
  { name; contents;
    lines = lines 0 (split_term (Str.regexp "\n") contents) }

let slurp chan =
  let rec read_all chunks =
    let buf = Bytes.init 4096 (fun _ -> '\x00') in
    match (input chan buf 0 (Bytes.length buf)) with
    | 0 -> Bytes.concat (Bytes.of_string "") (List.rev chunks)
    | n -> read_all (Bytes.sub buf 0 n :: chunks) in
  read_all []

let slurp_string chan =
  Bytes.to_string (slurp chan)

let of_file fname =
  source fname (slurp_string (open_in fname))

let of_string str =
  source "<input>" str


type linepart = {
  txt : string;
  lineno : int;
  startpos : int;
  endpos : int       
}

type source_loc =
| Line of linepart
| Multiline of linepart * linepart

let get_source_loc (Loc (src, p, q)) =
  (* As a special case, report the location of end-of-file as 
     the last character *)
  let (p, q) = match (p, q) with
    | (p, q) when p = q && p = String.length src.contents -> (p-1, q)
    | _ -> p, q in
  let line i s e = {
    txt = String.sub src.contents s (e - s);
    lineno = i;
    startpos = max 0 (p - s);
    endpos = min (e - s) (q - s)
  } in
  src.lines
  |> List.mapi (fun i (s, e) -> (i, s, e))
  |> List.filter (fun (i, s, e) -> p < e && s < q)
  |> function
    | [] -> failwith "internal error: bad location"
    | [(i, s, e)] -> Line (line i s e)
    | (i, s, e) :: rest ->
       let (i', s', e') = List.(hd (rev rest)) in
       Multiline (line i s e, line i' s' e')

let loc_srcname (Loc (src, _, _)) = src.name

let ptext ppf (Loc (src, p, q)) =
  Format.fprintf ppf "%s" (String.sub src.contents p (q - p))

let psrc_loc loc ppf = function
  | Line { lineno } -> 
     Format.fprintf ppf "%s:%d" (loc_srcname loc) (lineno + 1)
  | Multiline ({ lineno }, { lineno = lineno' }) ->
     Format.fprintf ppf "%s:%d-%d" (loc_srcname loc) (lineno + 1) (lineno' + 1)

let ploc ppf loc =
  psrc_loc loc ppf (get_source_loc loc)

let psource ppf loc =
  let srcloc = get_source_loc loc in
  let p loctxt { txt; lineno; startpos; endpos } =
    let txt = Str.replace_first (Str.regexp "\n") "" txt in
    Format.fprintf ppf "%s: %s\n%s  %s%s\n" 
      loctxt txt
      (String.make (String.length loctxt) ' ') 
      (String.make startpos ' ') (String.make (endpos - startpos) '^') in
  let loctxt = Format.asprintf "%a" (psrc_loc loc) srcloc in
  match srcloc with
  | Line l -> 
     p loctxt l
  | Multiline (({lineno} as l), ({lineno = lineno'} as l')) when lineno + 1 = lineno ->
     p loctxt l; p loctxt l'
  | Multiline (l, l') ->
     p loctxt l; Format.fprintf ppf "%s: ...\n" loctxt; p loctxt l'
    


(* contains a b -> a contains or is equal to b *)
let contains (Loc (s1, p, q)) (Loc (s2, p', q')) =
  s1 = s2 && p <= p' && q' <= q


let internal =
  let loc = { name = "<internal>"; contents = "?"; lines = [(0,1)] } in
  Loc (loc, 0, 1)


type location = t
module LocSet = Set.Make (struct type t = location let compare = compare end)
type set = LocSet.t

let one = LocSet.singleton

let join = LocSet.union

let extract s = List.hd (LocSet.elements s)

let empty = LocSet.empty
