(* --- Abstraction Component --- *)

open Abstracters
open Environ
open Term
open Coqterms

(* --- User configuration for lifting --- *)

type abstraction_config =
  {
    is_concrete : bool;
    env : env;
    args : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : abstraction_strategy list;
  }

(*--- Lifting ---*)

(*
 * Try to lift candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *)
val abstract_with_strategies : abstraction_config -> types list
