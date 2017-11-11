(* --- Abstraction Component --- *)

open Abstracters
open Environ
open Term
open Coqterms
open Candidates
open Abstractionconfig
open Proofdiff

(*--- Abstraction ---*)

(*
 * Try to abstract candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *)
val abstract_with_strategies : abstraction_config -> types list

(*
 * Try to abstract candidates in an inductive proof by their arguments
 * given the goal types of the old proof and the new proof.
 *
 * If there is nothing to abstract or if we cannot determine what to
 * abstract, then return the original list.
 *)
val try_abstract_inductive : lift_goal_diff -> candidates -> candidates
