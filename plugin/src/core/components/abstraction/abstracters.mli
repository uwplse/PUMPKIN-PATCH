(* --- Abstraction Strategies --- *)

open Term
open Environ
open Candidates

type abstraction_dimension = Arguments | Property

type abstraction_strategy

(* --- Top-level --- *)

(*
 * Substitute actual args with abstract args in candidates,
 * using a strategy to determine when to substitute.
 *)
val substitute_using :
 abstraction_strategy -> env -> types list -> types list -> candidates ->
 candidates

(*
 * Reduce candidates, using the abstraction strategy to determine
 * how to reduce
 *)
val reduce_all_using :
  abstraction_strategy -> env -> candidates -> candidates

(*
 * Filter candidates, using the abstraction strategy to determine
 * how to filter
 *)
val filter_using :
  abstraction_strategy -> env -> types -> candidates -> candidates

(* --- Recover options from an abstraction strategy --- *)

val kind_of_abstraction : abstraction_strategy -> abstraction_dimension

(*--- Strategies for abstracting arguments ---*)

(*
 * All strategies that reduce first
 *)
val reduce_strategies : abstraction_strategy list

(*
 * All strategies that don't reduce first
 *)
val no_reduce_strategies : abstraction_strategy list

(*
 * List of default strategies
 *)
val default_strategies : abstraction_strategy list

(*
 * List of the simplest strategies
 *)
val simple_strategies : abstraction_strategy list

(*--- Strategies for abstracting properties ---*)

(*
 * All strategies that reduce first
 *)
val reduce_strategies_prop : abstraction_strategy list

(*
 * All strategies that don't reduce first
 *)
val no_reduce_strategies_prop : abstraction_strategy list

(*
 * List of default strategies
 *)
val default_strategies_prop : abstraction_strategy list
