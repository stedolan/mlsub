type t = 
  | Conflict of Location.set * string * Location.set * string
  | SyntaxErr of Location.t
  | Unbound of Location.t * Symbol.t
let print ppf = function
  | (Conflict (la, a, lb, b)) ->
     (Location.LocSet.iter (Location.print ppf) la;
      Location.LocSet.iter (Location.print ppf) lb;
      Format.fprintf ppf "%s - %s\n%!" a b)
  | (SyntaxErr l) ->
     (Format.fprintf ppf "syntax error\n";
      Location.print ppf l)
  | Unbound (l, v) ->
     (Format.fprintf ppf "'%s' not in scope\n" (Symbol.to_string v);
      Location.print ppf l)
let excuse = Conflict (Location.empty, "?", Location.empty, "?")
