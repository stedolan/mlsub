open Variance
open Typector

(* Type automata and biunification *)

type state


val cons : polarity -> state Typector.Components.t -> state

val compile_type :
  context -> polarity -> typeterm -> state

val compile_type_pair :
  context -> typeterm -> state * state

val print_automaton :
  context -> (* FIXME should not need this *)
  string ->
  Format.formatter -> ((string -> state -> unit) -> unit) -> unit


val garbage_collect : state -> unit

val decompile_automaton : state list -> typeterm list

val flow_pair : unit -> state * state

val zero : polarity -> state

val constrain : Location.t -> state -> state -> Error.t list

type dstate

val clone : ((Location.set -> dstate -> state) -> 'a) -> 'a

val determinise :
  state list -> (state -> dstate) * dstate list

val minimise : dstate list -> dstate -> dstate

val entailed : dstate -> dstate -> bool
val subsumed :
  ((Variance.polarity -> state -> dstate -> bool) -> bool) ->
  bool
val find_reachable_dstates : dstate list -> dstate list
val optimise_flow : dstate list -> unit
