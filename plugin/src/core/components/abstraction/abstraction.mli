(* --- Abstraction Component --- *)

open Abstracters
open Environ
open Term
open Coqterms
open Candidates

(* --- Caller configuration for abstraction --- *)

type abstraction_config =
  {
    env : env;
    args_base : types list;
    args_goal : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : abstraction_strategy list;
  }

(*--- Abstraction ---*)

(*
 * Try to lift candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *)
val abstract_with_strategies : abstraction_config -> types list
