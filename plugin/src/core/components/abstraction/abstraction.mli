(* --- Abstraction Component --- *)

open Constr
open Evd
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
val abstract_case : (evar_map -> goal_case_diff -> candidates -> candidates) configurable

(* 
 * Replace all occurrences of the first term in the second term with Rel 1,
 * lifting de Bruijn indices as needed. The notion of term equality is modulo
 * alpha, casts, application grouping, and universes.
 *
 * By Nate Yazdani, from DEVOID.
 *)
val abstract_subterm : constr -> constr -> constr
