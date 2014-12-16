type caml_exp =
  | CVar of Symbol.t
  | CLambda of Symbol.t list * caml_exp
  | CApp of caml_exp * caml_exp list
  | CLet of Symbol.t * caml_exp * caml_exp
  | CAlloc of caml_exp array
  | CGetField of caml_exp * caml_exp
  | CRaw of string
  | CInt of int


let withtmp exp f =
  let s = Symbol.fresh "tmp" in
  CLet (s, exp, f (CVar s))

open Exp

let rec obj_shape k = function
  | [] -> []
  | (s, x) :: xs -> (s, k) :: obj_shape (k + 1) xs

       
let add_global (globs, seen) name x lower =
  if Hashtbl.mem seen x then
    Hashtbl.find seen x
  else
    let n = Symbol.fresh name in
    (Hashtbl.add seen x n; Hashtbl.add globs n (lower x); n)
  
let rec lower g = function
  | Var v -> CVar v
  | Lambda (args, body) ->
     CLambda ([args], lower g body)
  | Let (var, exp, body) ->
     CLet (var, lower g exp, lower g body)
  | App (fn, args) ->
     CApp (lower g fn, [lower g args])
  | Ascription (exp, ty) ->
     lower g exp
  | Unit ->
     CRaw "()"
  | Int n ->
     CInt n
  | Object fields ->
     let dict = add_global g "dict" (obj_shape 1 fields)
        (fun shape ->
         let ((m, s), table) = Dictionary.generate shape in
         CAlloc (Array.append [| CInt (m lsr 1); CInt s |]
                   (Array.map (function None -> CInt (-1) | Some n -> CInt n) table))) in
     CAlloc (Array.append [| CVar dict |] (Array.of_list (List.map (fun (s,x) -> lower g x) fields)))
  | GetField (obj, field) ->
     withtmp (lower g obj) (fun obj ->
       CApp (CRaw "get_field", [obj; CInt (Symbol.hash field)]))

open Format                   

let print_symbol ppf sym = fprintf ppf "%s" (Symbol.to_string sym)
let rec print_list sep pr ppf = function
  | [] -> ()
  | [x] -> pr ppf x
  | x :: xs -> fprintf ppf "%a%s@ %a" pr x sep (print_list sep pr) xs
                       
let rec emit_caml ppf = function
  | CVar v ->
     fprintf ppf "!%a" print_symbol v
  | CLambda (syms, body) ->
     fprintf ppf "(fun @[%a@] ->@ @[<v 2>%a@])" (print_list "" print_symbol) syms emit_caml body
  | CApp (exp, args) ->
     fprintf ppf "@[(%a %a)@]" emit_caml exp (print_list "" emit_caml) args
  | CLet (var, exp, body) ->
     fprintf ppf "@[<v 2>(let %a = %a in@ %a)@]" print_symbol var print_caml exp emit_caml body
  | CAlloc exps ->
     fprintf ppf "@[[|%a|]@]" (print_list ";" emit_caml) (Array.to_list exps)
  | CGetField (exp, field) ->
     fprintf ppf "@[%a.(%a)@]" emit_caml exp emit_caml field
  | CInt n ->
     fprintf ppf "!(%d)" n
  | CRaw s ->
     fprintf ppf "%s" s
and print_caml ppf e =
  fprintf ppf "@[<v 2>%a@]" emit_caml e


let to_caml ppf e =
  let globs = Hashtbl.create 20 and seen = Hashtbl.create 20 in
  let code = lower (globs, seen) e in
  fprintf ppf "let p n = Printf.printf \"%%d\\n%%!\" n\n";
  fprintf ppf "let (!) = Obj.magic\n";
  fprintf ppf "type dummy = Might_be_int | Might_be_addr of dummy * dummy\n";
  fprintf ppf "let lookup (t : dummy array) (k : int) : Obj.t =\n";
  fprintf ppf "  !t.(((k * (2 * (!t.(0)) + 1)) lsr !t.(1)) + 2)\n";
  fprintf ppf "let get_field (t : dummy array) (k : int) : Obj.t =\n";
  fprintf ppf "  !t.(!(lookup !t.(0) k))\n";
  Hashtbl.iter (fun name body ->
                fprintf ppf "let %a = %a@." print_symbol name print_caml body) globs;
  fprintf ppf "\n;;\n%a@." print_caml code
