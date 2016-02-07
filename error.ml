type t = 
  | Syntax of Location.t
  | Unmatched_closing_delim of Location.t
  | Mismatched_closing_delim of Location.t * Location.t
  | Unexpected_eof of Location.t

  | Conflict of Location.set * string * Location.set * string
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

  | Conflict (la, a, lb, b) ->
(*     (Location.LocSet.iter (Location.print ppf) la;
      Location.LocSet.iter (Location.print ppf) lb; *)
      Format.fprintf ppf "%s - %s" a b
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

let excuse = Unknown
