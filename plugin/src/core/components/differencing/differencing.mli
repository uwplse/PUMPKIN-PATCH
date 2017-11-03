(* --- Differencing Component --- *)

open Searchopts
open Proofdiff
open Candidates
open Environ
open Term

(* --- Differencing of types & terms --- *)

(*
 * Find the difference between two fixpoints
 * For now, this only detects a change in a single case of the fixpoint
 *)
val diff_fix : env -> types -> types -> candidates


(* --- Differencing of proofs --- *)

(*
 * Primitive differencing function
 *)
val find_difference : options -> goal_term_diff -> candidates

(*
 * Determine if two proof diffs are identical
 *)
val no_diff : options -> goal_proof_diff -> bool

