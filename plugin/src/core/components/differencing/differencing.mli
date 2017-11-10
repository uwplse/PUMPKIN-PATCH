(* --- Differencing Component --- *)

open Searchopts
open Proofdiff
open Candidates
open Environ
open Term
open Cutlemma
open Kindofchange

(* --- Differencing of types & terms --- *)

(*
 * Find the difference between the cases of two fixpoints
 *)
val diff_fix_cases : env -> types -> types -> candidates

(* --- Differencing of proofs --- *)

(*
 * Given a difference in proofs with goals and an optional lemma to cut by,
 * determine what has changed about the proof
 *)
val find_kind_of_change : goal_proof_diff -> cut_lemma option -> kind_of_change

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
