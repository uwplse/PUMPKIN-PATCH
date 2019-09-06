(* Search procedures *)

open Constr
open Proofdiff
open Searchopts
open Evd
open Stateutils

(*
 * Search for a patch given a default patch and a difference in proof cats
 * Return the default patch if we cannot find a patch
 * Otherwise, return any patch we can find
 *)
val search_for_patch :
  types -> options -> goal_proof_diff -> evar_map -> types state

