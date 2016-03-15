open Variance

type 'a printer = Format.formatter -> 'a -> unit

module SMap = Symbol.Map


type conflict =
  Location.set * Location.set * Error.conflict_reason

module Components : sig
  type +'a t

  val cmp_component : 'a t -> 'b t -> bool

  (* join Pos is least-upper-bound, join Neg is greatest-lower-bound. *)
  val join : polarity -> (polarity -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  (* lte Pos f a b is a <= b, lte Neg f a b is a >= b. f works the same way *)
  val lte : (polarity -> 'a -> 'b -> conflict list) -> 'a t -> 'b t -> conflict list
  (* same as lte, but returns only a boolean success rather than a list of errors *)
  val lte' : (polarity -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
    
  val pmap : (polarity -> 'a -> 'b) -> polarity -> 'a t -> 'b t
  val pfold : (polarity -> 'a -> 'r -> 'r) -> polarity -> 'a t -> 'r -> 'r

  val list_fields : 'a t -> (string * 'a) list

  val change_locations : Location.set -> 'a t -> 'a t
end


(* Syntax for types *)


type tyvar = Symbol.t

type typaram =
| TParam of Variance.variance option * Symbol.t
| TNoParam


type +'a tyarg =
| APos of 'a
| ANeg of 'a
| ANegPos of 'a * 'a
| ANone

type +'a tyargterm =
| VarSpec of 'a tyarg
| VarUnspec of 'a

type typeterm =
| TZero of Variance.polarity
| TNamed of tyvar * typeterm tyargterm list
| TCons of typeterm Components.t
| TAdd of Variance.polarity * typeterm * typeterm
| TRec of tyvar * typeterm
| TWildcard



(* Typing contexts *)

type +'a tybody =
| BParam of 'a
| BCons of 'a tybody Components.t

(* Types are defined only in terms of types
   with lower stamps *)
type stamp = private int

(* Stamp of builtin/fully-expanded types.
   Less than any other stamp. *)
val builtin_stamp : stamp

type context
val empty_context : context


val add_type_alias :
  'a -> (* FIXME: error reporting *)
  Symbol.t ->
  typaram list -> typeterm -> context -> context

val add_opaque_type :
  'a ->
  Symbol.t -> typaram list -> context -> context

val get_stamp :
  'a Components.t -> stamp

(* Can only be called for get_stamp != builtin_stamp.
   Enforces guardedness by returning a Components.t *)
val expand_alias :
  'a Components.t -> 'a tybody Components.t

val find_by_name :
  context -> Symbol.t -> (stamp * variance list) option

val name_of_stamp :
  context -> stamp -> Symbol.t

val print_typeterm : context -> typeterm printer

(* Constructing types *)

val ty_fun :
  (Location.LocSet.elt -> 'a) list ->
  ((Location.LocSet.elt -> 'a) * bool) SMap.t ->
  (Location.LocSet.elt -> 'a) -> Location.LocSet.elt -> 'a Components.t
val ty_obj :
  (Location.LocSet.elt -> 'a) SMap.t ->
  Location.LocSet.elt -> 'a Components.t
val ty_obj_l :
  (Symbol.t * (Location.LocSet.elt -> 'a)) list ->
  Location.LocSet.elt -> 'a Components.t

val ty_named :
  context ->
  Symbol.t ->
  typeterm tyargterm list -> 
  Location.LocSet.elt -> typeterm Components.t
val ty_named' :
  context -> Symbol.t -> 'b tyarg list -> Location.t -> 'b Components.t
val ty_base : context -> stamp -> 'a tyarg list -> Location.t -> 'a Components.t

