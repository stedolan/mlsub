type conflict_reason =
| Wrong_arity of int * int
| Unknown_kwarg of Symbol.t
| Missing_req_kwarg of Symbol.t
| Missing_field of Symbol.t
| Incompatible_type of [`Func | `Obj | `Base of Symbol.t] * [`Func | `Obj | `Base of Symbol.t]

type t = 
  | Syntax of Location.t
  | Unmatched_closing_delim of Location.t
  | Mismatched_closing_delim of Location.t * Location.t
  | Unexpected_eof of Location.t

  | Conflict of Location.t * Location.set * Location.set * conflict_reason
  | Unbound of [`Value | `Type] * Location.t * Symbol.t
  | Internal of string
  | Unknown
  | TooMany

exception Fatal of t

let fatal e = raise (Fatal e)
let internal s = fatal (Internal s)

let print ppf = 
  let open Location in
  let p fmt = 
    Format.kfprintf (fun ppf -> Format.fprintf ppf "\n") ppf fmt in
  function
  | Syntax l ->
     p "%a: Syntax error" ploc l;
     psource ppf l
  | Unmatched_closing_delim l ->
     p "%a: This '%a' is unmatched" ploc l ptext l;
     psource ppf l
  | Mismatched_closing_delim (lstart, lend) ->
     p "%a: This '%a' does not match the following '%a'" ploc lend ptext lstart ptext lend;
     psource ppf lstart;
     psource ppf lend
  | Unexpected_eof l ->
     p "%a: Unexpected end of input" ploc l;
     psource ppf l

  | Conflict (l, la, lb, reason) ->
     let psort ppf = function
       | `Func -> Format.fprintf ppf "function"
       | `Obj -> Format.fprintf ppf "object"
       | `Base s -> Format.fprintf ppf "'%s'" (Symbol.to_string s) in
     let found = match reason with
       | Wrong_arity _ | Unknown_kwarg _ | Missing_req_kwarg _ -> `Func
       | Missing_field _ -> `Obj
       | Incompatible_type (a, b) -> a in
     let required = match reason with
       | Wrong_arity _ | Unknown_kwarg _ | Missing_req_kwarg _ -> `Func
       | Missing_field _ -> `Obj
       | Incompatible_type (a, b) -> b in
     (match reason with
     | Wrong_arity (n, m) ->
        let required_args = match n with
          | 0 -> "no positional arguments"
          | 1 -> "one positional argument"
          | n -> Format.sprintf "%d positional arguments" n in
        let passed_args = match m with
          | 0 -> "none"
          | n -> Format.sprintf "%d" n in
        p "%a: This function takes %s, but is passed %s here" ploc l required_args passed_args
     | Unknown_kwarg k ->
        p "%a: This function does not take an argument called '%s'" ploc l (Symbol.to_string k)
     | Missing_req_kwarg k ->
        p "%a: This function requires an argument called '%s', missing here" ploc l (Symbol.to_string k)
     | Missing_field k ->
        p "%a: This object does not have a field '%s'" ploc l (Symbol.to_string k)
     | Incompatible_type (a, b) ->
        p "%a: This is a %a, but a %a is needed" ploc l psort a psort b);
     psource ppf l;
     let is_incompat = true || match reason with Incompatible_type _ -> true | _ -> false in
     la |> Location.LocSet.iter (fun la ->
       if is_incompat || not (Location.contains l la) then begin
         p "%a: the %a comes from here" ploc la psort found;
         psource ppf la
       end
     );
     lb |> Location.LocSet.iter (fun lb ->
       if is_incompat || not (Location.contains l lb) then begin
         p "%a: the %a is used here" ploc lb psort required;
         psource ppf lb
       end
     );

  | Unbound (sort, l, v) ->
     p "%a: The %s '%s' is not in scope" ploc l 
       (match sort with `Value -> "value" | `Type -> "type") (Symbol.to_string v);
     psource ppf l
  | Internal s ->
     p "Internal error: %s" s
  | Unknown ->
     p "I have no fucking idea what went wrong"
  | TooMany ->
     p "Too many errors, giving up"

