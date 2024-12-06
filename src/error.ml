type error_kind =
  | Syntax
  | Bad_name of [`Unknown|`Duplicate of Location.t|`Expected of [`Record|`Variant]] *
                [`Type|`Var] * string
  | Illformed_type of
      [ `Join_multi_cons
      | `Join_not_cons_or_var
      | `Join_poly
      | `Bound_not_simple
      | `Bound_not_cons
      | `Wrong_args of string * [`Arity of int * int | `Variance of int * string * [`Pos|`Neg]]
      | `Misused_param of Exp.variance_spec * string * [`Pos|`Neg]
      | `Recursion of [`Not_strictly_positive of string]
      | `Close_error of Types.close_typ_err
      | `Join_of_ty_param
      | `Must_be_closed
      ]
  | Conflict of [`Expr|`Pat|`Subtype|`Field_override of Typedefs.Nom_tag.t * Tuple_fields.field_name option] * Types.subtyping_error
  (* FIXME: Maybe delete Unknown_constructor, it's worse than a standard type error *)
  | Illformed_pat of [`Tag_required | `Duplicate_name of [`Var|`Field] * string * Location.t | `Orpat_different_names of string | `Wrong_length of int * int | `Unknown_cases | `Unknown_fields | `Unknown_constructor of string]
  | Incompatible_patterns of Location.t
  | Nonexhaustive of Exp.pat list list
  | Bad_tag of (Exp.tuple_tag option * Exp.tuple_tag list)
  | Bad_tuple_intro of [`Opt]
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
  let pp_ty = Typedefs.fmt_unit_typ in
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
  let vtype = function `Pos -> "covariantly" | `Neg -> "contravariantly" in
  let context = nest 2 (hardline ^^ pp_context loc) in
  (* FIXME: more of these could use context *)
  pp_loc loc ^^ pp ": " ^^ match err with
  | Syntax -> pp "syntax error" ^^ context
  | Bad_name (err,kind,name) ->
     pp "%s %s name %s"
       (match err with `Unknown -> "Unknown" | `Duplicate _ -> "Duplicate" | `Expected _ -> "Invalid")
       (match kind with `Type -> "type" | `Var -> "variable")
       name ^^
       (match err with
        | `Expected `Variant -> pp " (expected a variant type)"
        | `Expected `Record -> pp " (expected a record type)"
        | `Unknown | `Duplicate _ -> empty) ^^
       context ^^
     (match err with
      | `Unknown | `Expected _ -> empty
      | `Duplicate loc' ->
         hardline ^^ pp_loc loc' ^^ pp ": previously defined here" ^^
           nest 2 (hardline ^^ pp_context loc'))
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
  | Illformed_type (`Wrong_args (name, problem)) ->
     pp "The type %s " name ^^
       (match problem with
        | `Arity (0, _actual) -> pp "does not take arguments"
        | `Arity (exp, actual) -> pp "takes %d arguments, not %d" exp actual
        | `Variance (i, name, v) ->
           pp "does not take argument %d (%s) %s" (i+1) name (vtype v))
       ^^ context
  | Illformed_type (`Misused_param (vspec, name, v)) ->
     pp "The type parameter %s%s cannot be used here %s" (Print.variance_spec vspec) name (vtype v) ^^ context
  | Illformed_type (`Recursion (`Not_strictly_positive t)) ->
     pp "The type %s is used recursively in a non-strictly-positive position" t ^^ context
  | Illformed_type (`Close_error Join_contravariant) ->
     pp "This type contains a contravariant join of a polymorphic variable" ^^ context
  | Illformed_type (`Close_error Join_bad_scoping) ->
     pp "This type contains a scope-escaping join of a polymorphic variable" ^^ context
  | Illformed_type `Join_of_ty_param ->
     pp "Type definitions may not use joins of type parameters" ^^ context
  | Illformed_type `Must_be_closed ->
     pp "This type cannot use '...'" ^^ context
  | Bad_tag (tag, options) ->
     (match tag, options with
      | None, [] -> pp "Expected a tag"
      | None, others ->
         pp "Expected a tag " ^^ separate_map (pp " | ") Print.tuple_tag others
      | Some tag, [] ->
         pp "Unexpected tag " ^^ Print.tuple_tag tag
      | Some tag, others ->
         pp "Unexpected tag " ^^ Print.tuple_tag tag ^^
           pp ", expected " ^^ separate_map (pp " | ") Print.tuple_tag others)
       ^^ context
  | Bad_tuple_intro `Opt ->
     pp "Tuple construction cannot use optional fields" ^^ context
  | Conflict (_kind, err) ->
     let env = err.env in
     let env' = (fst err.env, []) in
     let conflict =
       match err.err with
        | Head Incompatible ->
           pp "Type error"
        (* FIXME improve tuple field names *)
        | Field_missing name ->
           pp "The field '%s' is missing." (Tuple_fields.string_of_field_name name)
        | Field_extra (Some name) ->
           pp "A surplus field '%s' is present." (Tuple_fields.string_of_field_name name)
        | Field_extra None ->
           pp "Surplus fields are present."
        | Head (Expected_tag (tag, tags')) ->
           (* FIXME reword (e.g. int vs. bool) *)
           let tagname = Typedefs.Cons1.Tag.to_string in
           let tag = match tag with None -> string "no tag" | Some t -> string "tag " ^^ Print.tuple_tag t in
           pp "The tag should be " ^^ separate_map (pp "|") (fun t -> pp "%s" (tagname t)) tags' ^^ pp ", but " ^^ tag ^^ string " is present."
        | Head (Args `Too_few) ->
           pp "Too few arguments."
        | Head (Args `Too_many) ->
           pp "Too many arguments."
        | Head (Args `Wrong_number) ->
           pp "Wrong number of arguments."
     in
     conflict ^^
     nest 2 (hardline ^^ pp_context loc) ^^
     nest 2 (hardline ^^ pp "   found:" ^^ group (nest 3 (break 1 ^^ pp_ty ~env:env' err.lhs))) ^^
     nest 2 (hardline ^^ pp "expected:" ^^ group (nest 3 (break 1 ^^ pp_ty ~env:env' err.rhs))) ^^
     (match err.located with
      | ((lty,lloc),(rty,rloc)) ->
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
  | Illformed_pat `Tag_required ->
     pp "This pattern is missing a tag" ^^ context
  | Illformed_pat (`Duplicate_name (kind, k, other)) ->
     let kind = match kind with `Var -> "variable" | `Field -> "field" in
     pp "The %s name %s is already in use:" kind k ^^ context ^^
       hardline ^^ pp "as it is previously bound here:" ^^
       nest 2 (hardline ^^ pp_context other)
  | Illformed_pat (`Wrong_length (found, expected)) ->
     pp "Expected %d patterns but found %d:" expected found ^^ context
  | Illformed_pat `Unknown_cases ->
     pp "Cannot determine which cases this pattern matches" ^^ context
  | Illformed_pat `Unknown_fields ->
     pp "Cannot determine which fields this pattern matches" ^^ context
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
