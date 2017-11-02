(* Lifting strategies *)

open Abstraction
open Environ
open Term
open Coqterms

type candidates = types list
type arg_subst
type abstraction_strategy

(* --- User configuration for lifting --- *)

type lift_config =
  {
    is_concrete : bool;
    env : env;
    args : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : abstraction_strategy list;
  }

(*--- Lifting arguments ---*)

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

(*--- Lifting properties ---*)

(*
 * All strategies that reduce first
 *)
val reduce_strategies_prop : types -> abstraction_strategy list

(*
 * All strategies that don't reduce first
 *)
val no_reduce_strategies_prop : types -> abstraction_strategy list

(*
 * List of default strategies
 *)
val default_strategies_prop : types -> abstraction_strategy list

(*--- Lifting ---*)

(*
 * Try to lift candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *)
val lift_with_strategies : lift_config -> types list
