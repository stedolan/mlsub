type caml_exp =
  | CVar of Symbol.t
  | CLambda of Symbol.t list * caml_exp
  | CApp of caml_exp * caml_exp list
  | CLet of Symbol.t * caml_exp * caml_exp
  | CRaw of string


let withtmp exp f =
  let s = Symbol.fresh "tmp" in
  CLet (s, exp, f s)

open Exp
let rec lower = function
  | Var v -> CVar v
  | Lambda (args, body) ->
     CLambda ([args], lower body)
  | Let (var, exp, body) ->
     CLet (var, lower exp, lower body)
  | App (fn, args) ->
     CApp (lower fn, [lower args])
  | Ascription (exp, ty) ->
     lower exp
  | Unit ->
     CRaw "()"



open Format                   

let print_symbol ppf sym = fprintf ppf "%s" (Symbol.to_string sym)
let rec print_list sep pr ppf = function
  | [] -> ()
  | [x] -> pr ppf x
  | x :: xs -> fprintf ppf "%a%s@ %a" pr x sep (print_list sep pr) xs
                       
let rec emit_caml ppf = function
  | CVar v ->
     print_symbol ppf v
  | CLambda (syms, body) ->
     fprintf ppf "fun @[%a@] ->@ @[<v 2>%a@]" (print_list "" print_symbol) syms emit_caml body
  | CApp (exp, args) ->
     fprintf ppf "@[%a %a@]" emit_caml exp (print_list "" emit_caml) args
  | CLet (var, exp, body) ->
     fprintf ppf "@[<v 2>let %a = %a in@ %a@]" print_symbol var print_caml exp emit_caml body
  | CRaw s ->
     fprintf ppf "%s" s
and print_caml ppf e =
  fprintf ppf "@[<v 2>%a@]" emit_caml e


let to_caml ppf e =
  fprintf ppf "%a@." print_caml (lower e)
