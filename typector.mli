type polarity = Pos | Neg
type 'a printer = Format.formatter -> 'a -> unit

val polneg : polarity -> polarity
val polmul : polarity -> polarity -> polarity
val pol_flip : ('a -> 'a -> 'b) -> polarity -> 'a -> 'a -> 'b


(* FIXME *)
module SMap : Map.S with type key = int


module Components : sig
  type 'a t

  val cmp_component : 'a t -> 'b t -> bool

  (* join Pos is least-upper-bound, join Neg is greatest-lower-bound. *)
  val join : polarity -> (polarity -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  (* lte Pos f a b is a <= b, lte Neg f a b is a >= b. f works the same way *)
  val lte : (polarity -> 'a -> 'b -> Error.t list) -> 'a t -> 'b t -> Error.t list
    
  val pmap : (polarity -> 'a -> 'b) -> polarity -> 'a t -> 'b t
  val pfold : (polarity -> 'a -> 'r -> 'r) -> polarity -> 'a t -> 'r -> 'r

  val print : (polarity -> 'a printer) -> polarity -> 'a t printer
  val list_fields : 'a t -> (string * 'a) list

  val locations : 'a t -> Location.set
  val change_locations : Location.set -> 'a t -> 'a t
end

val ty_list :
  (Location.LocSet.elt -> 'a) -> Location.LocSet.elt -> 'a Components.t
val ty_fun :
  (Location.LocSet.elt -> 'a) list ->
  ((Location.LocSet.elt -> 'a) * bool) SMap.t ->
  (Location.LocSet.elt -> 'a) -> Location.LocSet.elt -> 'a Components.t
val ty_obj :
  (Location.LocSet.elt -> 'a) SMap.t ->
  Location.LocSet.elt -> 'a Components.t
val ty_base : Symbol.t -> Location.LocSet.elt -> 'a Components.t

