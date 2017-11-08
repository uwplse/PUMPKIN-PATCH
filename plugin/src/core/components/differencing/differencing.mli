(* --- Differencing Component --- *)

open Searchopts
open Proofdiff
open Candidates
open Environ
open Term

(* --- Differencing of types & terms --- *)

(*
 * Find the difference between the cases of two fixpoints
 *)
val diff_fix_cases : env -> types -> types -> candidates


(* --- Differencing of proofs --- *)

(*
 * Primitive differencing function
 *)
val find_difference : options -> goal_term_diff -> candidates

(*
 * Determine if two proof diffs are identical
 *)
val no_diff : options -> goal_proof_diff -> bool

(*
 * Return the identity candidates applied to the type
 * of the new proof in the diff
 *)
val identity_candidates : goal_proof_diff -> candidates

(* --- Recursive differencing --- *)

(*
 * Using some differencing function between terms,
 * recursively difference the arguments
 *)
val diff_args :
  (types -> types -> candidates) -> types array -> types array -> candidates
