open Variance
open Typector

val ty_add : polarity -> Exp.typeterm list -> Exp.typeterm


module TypeLat : sig
  type 'a t
  val lift : 'a Components.t -> 'a t
  val join : polarity -> (polarity -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val join_ident : 'a t

  val lte_pn : ('a -> 'a -> Error.t list) -> 'a t -> 'a t -> Error.t list
  val lte_np : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val subs : polarity -> (polarity -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

  val pmap : (polarity -> 'a -> 'b) -> polarity -> 'a t -> 'b t
  val pfold : (polarity -> 'a -> 'r -> 'r) -> polarity -> 'a t -> 'r -> 'r
  val iter : (polarity -> 'a -> unit) -> polarity -> 'a t -> unit

  val print : (polarity -> 'a printer) -> polarity -> 'a t printer
  val list_fields : 'a t -> (string * 'a) list

  val to_typeterm : polarity -> Exp.typeterm t -> Exp.typeterm
  val change_locations : Location.set -> 'a t -> 'a t
end
