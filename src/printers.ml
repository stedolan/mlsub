let p = Format.fprintf


let pp_comma ppf () = Format.fprintf ppf ",@ "

let printp paren pr ppf = let open Format in
  let openbox ppf = if paren then fprintf ppf "@[(" else fprintf ppf "@[" in
  let closebox ppf = if paren then fprintf ppf "@])" else fprintf ppf "@]" in
  openbox ppf;
  kfprintf closebox ppf "%a" pr


let pp_sym ppf s = p ppf "%s" (Symbol.to_string s)

let rec pp_pat ppf : Exp.pat -> unit = function
  | (_, None) -> p ppf "?"
  | (_, Some pat) -> pp_rpat ppf pat

and pp_rpat ppf = let open Exp in function
  | PWildcard -> p ppf "_"
  | PBind (v, (_, Some PWildcard)) -> pp_sym ppf v
  | PBind (v, pat) -> p ppf "??" (* FIXME *)
  | PObject (tag, fields) ->
     let pp_tag ppf = function
       | None -> ()
       | Some tag -> p ppf "'%s" (Symbol.to_string tag) in
     let pp_field ppf (s, pat) =
       p ppf "%a = %a" pp_sym s pp_pat pat in
     let pp_fields ppf = function
       | [] -> ()
       | fields -> p ppf "(%a)" (Format.pp_print_list ~pp_sep:pp_comma pp_field) fields in
     p ppf "%a%a" pp_tag tag pp_fields fields
  | PInt n -> p ppf "%d" n
  | PNil -> p ppf "[]"
  | PCons (x, xs) -> p ppf "%a :: %a" pp_pat x pp_pat xs
  | PAlt (p1, p2) -> p ppf "(%a | %a)" pp_pat p1 pp_pat p2



open Variance
let print_comp pb ctx pr ppf = 
  let open Typector in
  let open Components in function
  | Func (pos, kwargs, reqs, (l, res)) ->
     let args = List.map (fun (l, a) -> (None, Some a)) pos @
       (SMap.merge (fun k arg req -> match arg, req with
        | Some (l, a), None -> Some (Some (Symbol.to_string k ^ "?"), Some a)
        | Some (l, a), Some () -> Some (Some (Symbol.to_string k), Some a)
        | None, Some () -> Some (Some (Symbol.to_string k), None)
        | None, None -> None) kwargs reqs |> SMap.bindings |> List.map (fun (a, b) -> b)) in
     let need_paren = match args with [None, Some _] -> false | _ -> true in
     let pr_arg ppf = function
       | None, None -> ()
       | None, Some t -> Format.fprintf ppf "%a" (pr need_paren) t
       | Some name, Some t -> Format.fprintf ppf "%s : %a" name (pr need_paren) t
       | Some name, None -> Format.fprintf ppf "%s : <err>" name in
     let comma ppf () = Format.fprintf ppf ",@ " in
     Format.fprintf ppf (if pb then "%a -> %a" else "(%a -> %a)")
       (printp need_paren (Format.pp_print_list ~pp_sep:comma pr_arg)) args
       (pr false) res
  | Object (tagged, untagged) ->
     let rec pfield ppf = function
       | [] -> ()
       | [f, (_,x)] ->
          Format.fprintf ppf "%s :@ %a" (Symbol.to_string f) (pr false) x
       | (f, (_,x)) :: xs ->
          Format.fprintf ppf "%s :@ %a,@ %a" (Symbol.to_string f) (pr false) x pfield xs in
     let ptagged etag ppf (tag, o) =
       let tag = match tag with None -> etag | Some t -> "'" ^ Symbol.to_string t in
       match SMap.bindings o with
       | [] -> Format.fprintf ppf "%s" tag
       | bs -> Format.fprintf ppf "%s(%a)" tag pfield bs in
     let cases =
       (SMap.bindings tagged |> List.map (fun (tag, o) -> (Some tag, o))) @
       (match untagged with Some o -> [None, o] | None -> []) in
     (match cases with
     | [] -> Format.fprintf ppf "nothing_obj"
     | [c] -> ptagged "" ppf c
     | cs -> Format.fprintf ppf (if pb then "%a" else "(%a)") (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "%s" " | ") (ptagged "..")) cs)
  | Base (l, s, td, []) ->
     Format.fprintf ppf "%s" (Symbol.to_string (name_of_stamp ctx s))
  | Base (l, s, (TAlias (_, params, _) | TOpaque (_, params)), args) ->
     let pb = match args with [_] -> true | _ -> false in
     let print_arg ppf = function
       | VPos, APos t -> Format.fprintf ppf "%a" (pr pb) t
       | _, APos t -> Format.fprintf ppf "+%a" (pr pb) t 
       | VNeg, ANeg t -> Format.fprintf ppf "%a" (pr pb) t
       | _, ANeg t -> Format.fprintf ppf "-%a" (pr pb) t
       | _, ANegPos (s, t) -> Format.fprintf ppf "-%a +%a" (pr false) s (pr false) t
       | _, ANone -> Format.fprintf ppf "_" in
     Format.fprintf ppf "%s[%a]" (Symbol.to_string (name_of_stamp ctx s)) 
       (Format.pp_print_list ~pp_sep:pp_comma print_arg) 
       (List.map2 (fun (v, _) b -> v , b) (Array.to_list params) args)


open Typector
let needs_paren p = function
  | TRec _ -> true
  | TAdd (p', t1, t2) -> not (p = p')
  | TCons (Components.Func _) -> true
  | _ -> false

(* pb is true: delimited by context
   pb is false: this should this be self-delimiting. *)
let rec print_typeterm ctx pb ppf = let open Format in function
  | TZero Pos -> fprintf ppf "nothing"
  | TZero Neg -> fprintf ppf "any"
  | TNamed (v, []) ->
     fprintf ppf "%s" (Symbol.to_string v)
  | TNamed (v, args) -> 
     let pb' = match args with [_] -> true | _ -> false in
     let print_arg ppf = function
       | VarSpec (APos t) -> fprintf ppf "+%a" (print_typeterm ctx pb') t
       | VarSpec (ANeg t) -> fprintf ppf "-%a" (print_typeterm ctx pb') t
       | VarSpec (ANegPos (s, t)) -> fprintf ppf "-%a +%a"
          (print_typeterm ctx false) s (print_typeterm ctx false) t
       | VarSpec (ANone) -> fprintf ppf "_"
       | VarUnspec t -> fprintf ppf "%a" (print_typeterm ctx pb') t in
     fprintf ppf "%s[%a]" (Symbol.to_string v) (Format.pp_print_list ~pp_sep:pp_comma print_arg) args
  | TCons cons ->
     fprintf ppf "@[%a@]" (print_comp pb ctx (print_typeterm ctx)) cons
  | TAdd (p, _, _) as t ->
     if pb then
       fprintf ppf "@[%a@]" (print_sum p ctx) t
     else
       fprintf ppf "@[(%a)@]" (print_sum p ctx) t
  | TRec (v, t) ->
    (* FIXME paren placement ok? *)
    fprintf ppf "rec %s = %a" (Symbol.to_string v) (print_typeterm ctx false) t
  | TWildcard ->
    fprintf ppf "_"
and print_sum p ctx ppf = let open Format in function
| TAdd (p', t1, t2) when p' = p ->
   fprintf ppf "%a %s@ %a"
     (print_sum p ctx) t1
     (match p with Pos -> "|" | Neg -> "&")
     (print_sum p ctx) t2
| t -> print_typeterm ctx false ppf t


let pp_typeterm ctx = print_typeterm ctx true
