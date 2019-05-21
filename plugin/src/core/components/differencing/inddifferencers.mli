(* --- Differencing of Inductive Proofs --- *)

open Differencers
open Searchopts
open Proofdiff
open Evd

(*
 * Difference an inductive proof.
 *
 * That is, break the proof into cases and difference each case separately.
 * In each case, abstract if necessary, then adjust the patch so it
 * type-checks in the original environment.
 *
 * Use the options to determine how to abstract and how much to adjust by.
 *
 * Use the old goal_proof_diff along with the options to determine how
 * to update the goals for the next iteration.
 *)
val diff_inductive :
  (evar_map -> proof_differencer) configurable ->
  goal_proof_diff ->
  (evar_map -> ind_proof_differencer) configurable
