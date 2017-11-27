(* --- Abstraction Component --- *)

open Abstracters
open Environ
open Term
open Coqterms
open Candidates
open Abstractionconfig
open Proofdiff
open Searchopts

(*--- Abstraction ---*)

(*
 * Try to abstract candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *)
val abstract_with_strategies : abstraction_config -> types list

(*
 * Abstract candidates in a case of an inductive proof.
 * Use the options to determine whether or not to abstract,
 * and how to abstract if we should abstract.
 * If there is nothing to abstract or if we cannot determine what to
 * abstract, then return the original list.
 *)
val abstract_case : (goal_case_diff -> candidates -> candidates) configurable
