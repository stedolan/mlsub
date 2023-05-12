type error_kind =
  | Syntax
  | Bad_name of [`Unknown|`Duplicate] * [`Type|`Var] * string
  | Illformed_type of [`Join_multi_cons | `Join_not_cons_or_var | `Join_poly | `Bound_not_simple | `Bound_not_cons | `Bound_crosses_levels of string]
  | Conflict of [`Expr|`Pat|`Subtype] * Types.subtyping_error

  | Illformed_pat of [`Duplicate_name of string * Location.t | `Orpat_different_names of string | `Wrong_length of int * int | `Unknown_cases | `Unknown_constructor of string]
  | Incompatible_patterns of Location.t
  | Nonexhaustive of Exp.pat list list
  | Unused_pattern

type t = Location.t * error_kind

exception Fail of t

let fail loc k = raise (Fail (loc, k))

(* FIXME: for now, log always Fail's *)
let log ~loc e = fail loc e

let or_raise kind loc = function
  | Ok () -> ()
  | Error c -> fail loc (Conflict (kind, c))

let pp_err input loc err : PPrint.document =
  let open PPrint in
  let pp fmt = Format.ksprintf PPrint.utf8string fmt in
  let pp_ty ~env t =
    Typedefs.unparse_gen_typ t
      ~env
      ~neg:(fun ~env:_ () -> Typedefs.(mktyexp (named_type "_")))
      ~pos:(fun ~env:_ () -> Typedefs.(mktyexp (named_type "_")))
    |> Print.tyexp
  in
  let pp_loc (loc : Location.t) =
    (* FIXME character numbers also *)
    separate_map (pp ",") (fun (loc : Location.span) ->
      pp "%s:%d" loc.loc_start.pos_fname loc.loc_start.pos_lnum) loc in
  let pp_context (loc : Location.t) =
    separate_map (break 0) (fun (loc : Location.span) ->
    if loc.loc_start.pos_lnum = 0 then empty else
      let line = List.nth input (loc.loc_start.pos_lnum - 1) in
      let offs = loc.loc_start.pos_cnum - loc.loc_start.pos_bol in
      let cend =
        if loc.loc_end.pos_lnum = loc.loc_start.pos_lnum then
          loc.loc_end.pos_cnum - loc.loc_start.pos_bol 
        else
          String.length line in
      pp "%s" line ^^
      hardline ^^ pp "%*s" cend (String.make (cend-offs) '^')) loc
  in
  let context = nest 2 (hardline ^^ pp_context loc) in
  (* FIXME: more of these could use context *)
  pp_loc loc ^^ pp ": " ^^ match err with
  | Syntax -> pp "syntax error" ^^ context
  | Bad_name (err,kind,name) ->
     pp "%s %s name %s"
       (match err with `Unknown -> "Unknown" | `Duplicate -> "Duplicate")
       (match kind with `Type -> "type" | `Var -> "variable")
       name ^^ context
  | Illformed_type `Join_multi_cons ->
     pp "Joins may only contain one non-variable type" ^^ context
  | Illformed_type `Join_not_cons_or_var ->
     pp "Joins may only contain constructed types and variables" ^^ context
  | Illformed_type `Join_poly ->
     pp "Joins may not contain polymorphic types" ^^ context
  | Illformed_type `Bound_not_simple ->
     pp "Bounds must be simple types" ^^ context
  | Illformed_type `Bound_not_cons ->
     pp "Bounds must be constructed types" ^^ context
  | Illformed_type (`Bound_crosses_levels n) ->
     pp "Rigid variable %s not allowed in join with variable bound earlier" n ^^ context
  | Conflict (_kind, err) ->
     let env = err.env in
     let conflict =
       match err.err with
        | Incompatible ->
           pp "Type error"
        (* FIXME improve tuple field names *)
        | Fields (`Missing name) ->
           pp "The field '%s' is missing." (Tuple_fields.string_of_field_name name)
        | Fields (`Extra (Some name)) ->
           pp "A surplus field '%s' is present." (Tuple_fields.string_of_field_name name)
        | Fields (`Extra None) ->
           pp "Surplus fields are present."
        | Tags (tag, tags') ->
           let tag = match tag with None -> "no tag" | Some s -> "tag " ^ s in
           pp "The tag should be " ^^ separate_map (pp "|") (pp "%s") tags' ^^ pp ", but %s is present." tag
        | Args (`Missing name) ->
           pp "The argument '%s' is missing." (Tuple_fields.string_of_field_name name)
        | Args (`Extra (Some name)) ->
           pp "A surplus argument '%s' is present." (Tuple_fields.string_of_field_name name)
        | Args (`Extra None) ->
           pp "Surplus arguments are present."
     in
     conflict ^^
     nest 2 (hardline ^^ pp_context loc) ^^
     nest 2 (hardline ^^ pp "   found:" ^^ group (nest 3 (break 1 ^^ pp_ty ~env err.lhs))) ^^
     nest 2 (hardline ^^ pp "expected:" ^^ group (nest 3 (break 1 ^^ pp_ty ~env err.rhs))) ^^
     (match err.located with
      | None -> empty
      | Some ((lty,lloc),(rty,rloc)) ->
         let lty = nest 4 (break 1 ^^ pp_ty ~env lty) ^^ break 1 in
         let rty = nest 4 (break 1 ^^ pp_ty ~env rty) ^^ break 1 in
         let l_interest = not (Location.equal lloc loc) in
         let r_interest = not (Location.equal rloc loc) in
         match l_interest, r_interest with
         | true, true ->
           hardline ^^
           group (pp "This" ^^ lty ^^ pp "comes from " ^^ pp_loc lloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context lloc) ^^
           hardline ^^
           group (pp "but is used as" ^^ rty ^^ pp "at " ^^ pp_loc rloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context rloc)
         | true, false ->
           hardline ^^
           group (pp "This" ^^ lty ^^ pp "comes from " ^^ pp_loc lloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context lloc) ^^
           hardline ^^
           group (pp "but is used as" ^^ rty)
         | false, true ->
           hardline ^^
           group (pp "This" ^^ lty ^^ pp "is used as" ^^ rty ^^ pp "at " ^^ pp_loc rloc ^^ pp ":") ^^
             nest 2 (hardline ^^ pp_context rloc)
         | false, false -> empty
     )
  | Incompatible_patterns other_loc ->
     pp "This pattern:" ^^ context ^^
       hardline ^^ pp "is incompatible with the pattern at " ^^ pp_loc other_loc ^^ pp ":" ^^
       nest 2 (hardline ^^ pp_context other_loc)
  | Illformed_pat (`Duplicate_name (k, other)) ->
     pp "The variable name %s is already in use:" k ^^ context ^^
       hardline ^^ pp "as it is previously bound here:" ^^
       nest 2 (hardline ^^ pp_context other)
  | Illformed_pat (`Wrong_length (found, expected)) ->
     pp "Expected %d patterns but found %d:" expected found ^^ context
  | Illformed_pat `Unknown_cases ->
     pp "Cannot determine which cases this pattern matches" ^^ context
  | Illformed_pat (`Orpat_different_names k) ->
     pp "The variable %s must be bound on both sides of this or-pattern" k ^^ context
  | Illformed_pat (`Unknown_constructor s) ->
     (* FIXME should show source of ty *)
     pp "This type does not have a constructor %s" s ^^ context
  | Nonexhaustive missing ->
     pp "Some cases of this pattern-match are missing:" ^^ context  ^^
     hardline ^^ pp "The following cases are unhandled:" ^^ hardline ^^
       separate_map (break 1) (fun ps ->
         string "| " ^^ group (separate_map (comma ^^ break 1) Print.pat ps)) missing
  | Unused_pattern ->
     pp "This pattern is unused" ^^ context
