
(* Later, maybe intern these? *)

(* FIXME: preserve ordering of tuple fields in mixtures,
   to avoid screwing up evaluation order.
   (Alt: ban mixtures in the parser) *)

(* FIXME: make positional precede kw when mixed *)

type symbol = string
module SymMap = Map.Make (struct type t = string let compare = compare end)

type field_name = Field_positional of int | Field_named of symbol
module FieldMap = Map.Make (struct type t = field_name let compare = compare end)

let equal_field_name = (=)

let string_of_field_name = function
  | Field_named s -> s
  | Field_positional i -> Printf.sprintf ".%d" i

type +'a tuple_fields =
  { fields : 'a FieldMap.t;
    fnames : field_name list;
    fopen : [`Open|`Closed] }

type 'a field_syntax =
  | Fpos of 'a
  | Fnamed of symbol * 'a
  | Fdots
  | Fempty

let rec collect_fields npos fields fnames_rev = function
  | ([] | [Fempty] | [Fdots]) as tail ->
     let fopen = match tail with [Fdots] -> `Open | _ -> `Closed in
     { fields; fnames = List.rev fnames_rev; fopen }
  | field :: rest ->
     let name, value, npos =
       match field with
       | Fpos v -> Field_positional npos, v, npos+1
       | Fnamed (s, v) -> Field_named s, v, npos
       | Fdots -> failwith "'...' can only appear at the end"
       | Fempty -> assert false in
     let fields =
       if FieldMap.mem name fields then
         failwith ("duplicate field names " ^ string_of_field_name name);
       FieldMap.add name value fields in
     collect_fields npos fields (name :: fnames_rev) rest

let collect_fields fs = collect_fields 0 FieldMap.empty [] fs

let equal_fields f ps qs =
  FieldMap.equal f ps.fields qs.fields &&
  ps.fnames = qs.fnames &&
  ps.fopen = qs.fopen

let map_fields f fs =
  { fs with fields = FieldMap.mapi (fun fn x -> f fn x) fs.fields }

let iter_fields f fs =
  ignore (map_fields f fs)

let fold_fields f (acc : 'acc) fs =
  List.fold_left (fun acc n ->
      f acc n (FieldMap.find n fs.fields)) acc fs.fnames

let fold_right_fields f fs (acc : 'acc) =
  List.fold_right (fun n acc ->
      f n (FieldMap.find n fs.fields) acc) fs.fnames acc

let list_fields fs =
  List.rev (fold_fields (fun acc fn x -> (fn, x) :: acc) [] fs)

let fields_of_list ~fopen fs =
  let fields =
    List.fold_left (fun acc (fn, x) ->
      if FieldMap.mem fn acc then invalid_arg "duplicate field names";
      FieldMap.add fn x acc) FieldMap.empty fs in
  { fopen; fields; fnames = List.map fst fs }
    

let empty_fields = collect_fields [Fdots]

let is_empty fs =
  match fs.fnames with
  | [] -> true
  | _ :: _ -> false

let get_field fs f =
  FieldMap.find f fs.fields

let get_field_opt fs f =
  FieldMap.find_opt f fs.fields


let merge_fields ~left ~both ~right ~extra fs_l fs_r =
  let rec go_l remaining_r accfields accnames extra_l names_l =
    match names_l with
    | n :: names_l ->
       let f_l = FieldMap.find n fs_l.fields in
       let res, extra_l, remaining_r =
         match FieldMap.find_opt n remaining_r with
         | Some f_r -> both n f_l f_r, extra_l, FieldMap.remove n remaining_r
         | None -> left n f_l, `Extra, remaining_r in
       begin match res with
       | None -> go_l remaining_r accfields accnames extra_l names_l
       | Some res ->
          go_l remaining_r (FieldMap.add n res accfields) (n :: accnames) extra_l names_l
       end
    | [] ->
       let rec go_r remaining_r accfields accnames extra_r names_r =
         match names_r with
         | n :: names_r when not (FieldMap.mem n remaining_r) ->
            go_r remaining_r accfields accnames extra_r names_r
         | n :: names_r ->
            assert (not (FieldMap.mem n fs_l.fields));
            let f_r = FieldMap.find n remaining_r in
            let remaining_r = FieldMap.remove n remaining_r in
            let res = right n f_r in
            begin match res with
            | None -> go_r remaining_r accfields accnames `Extra names_r
            | Some res ->
               go_r remaining_r (FieldMap.add n res accfields) (n :: accnames) `Extra names_r
            end
         | [] ->
            assert (List.length accnames = FieldMap.cardinal accfields);
            { fnames = List.rev accnames;
              fields = accfields;
              fopen = extra ((fs_l.fopen, extra_r), (fs_r.fopen, extra_l)) } in
       go_r remaining_r accfields accnames `Subset fs_r.fnames in
  go_l fs_r.fields FieldMap.empty [] `Subset fs_l.fnames

(* May fail, if one side has extra fields and the other is closed *)
let union ~left ~right ~both sf tf =
  begin match merge_fields sf tf
    ~left:(fun _ s -> Some (left s))
    ~right:(fun _ t -> Some (right t))
    ~both:(fun _ s t -> Some (both s t))
    ~extra:(function
      | ((`Closed, `Extra), _)
      | (_, (`Closed, `Extra)) -> raise_notrace Exit
      | (`Open, _), (`Open, _) -> `Open
      | (`Closed, `Subset), (`Closed, `Subset) -> `Closed
      | (`Closed, `Subset), (`Open, _) -> `Closed
      | (`Open, _), (`Closed, `Subset) -> `Closed
    )
  with
  | st -> Some st
  | exception Exit -> None
  end

let inter ~both sf tf =
  (merge_fields sf tf
     ~left:(fun _ _s -> None)
     ~right:(fun _ _t -> None)
     ~both:(fun _ s t -> Some (both s t))
     ~extra:(function
       | (`Closed, `Subset), (`Closed, `Subset) -> `Closed
       | _ -> `Open))
