(* --- Differencing Component --- *)

(*
 * TODO when done refactoring this, hide
 * anything that doesn't need to be exposed.
 * Same holds for type definitions (in differencers).
 *)

open Proofcat
open Searchopts
open Proofdiff
open Candidates
open Environ
open Term
open Cutlemma
open Differencers

(* --- Differencing of types & terms --- *)

(*
 * Find the difference between the cases of two fixpoints
 *)
val diff_fix_cases : env -> term_differencer

(* --- Differencing of proofs --- *)

(*
 * Primitive differencing function
 *)
val find_difference : options -> proof_differencer

(*
 * Determine if two proof diffs are identical
 *)
val no_diff : options -> proof_diff_predicate

(*
 * Return the identity candidates applied to the type
 * of the new proof in the diff
 *)
val identity_candidates : proof_differencer

(* --- Recursive differencing --- *)

(*
 * Try to difference with one differencer
 * If that fails, then try the next one, and so on
 *)
val try_chain_diffs :
  ('a candidate_differencer) list -> 'a proof_diff -> candidates

(*
 * Reduce and then diff
 * If reducing has no effect, then give up to prevent inifinite recursion
 *)
val diff_reduced : proof_differencer -> proof_differencer

(*
 * Convert a proof differencer to a term differencer
 *
 * In other words, update the goals and terms of the current diff using
 * the supplied options, then apply the supplied differencing function
 * to the difference in terms.
 *)
val diff_terms :
  proof_differencer -> goal_proof_diff -> options -> term_differencer

(*
 * Using some term differencer, recursively difference the arguments
 * Return a flattened list of all differences
 *)
val diff_args_flat : term_differencer -> flat_args_differencer

(*
 * Using some term differencer, recursively difference the arguments
 * Don't flatten the resulting list
 *)
val diff_args : term_differencer -> args_differencer

(*
 * Apply some differencing function
 * Filter the result using the supplied modifier
 *)
val filter_diff : ('b -> 'b) -> ('a, 'b) differencer -> ('a, 'b) differencer

(*
 * If the proofs are applications (f args) and (f' args'),
 * then recursively diff the functions and/or arguments.
 *
 * Use the options to determine how to combine the results.
 *)
val diff_app :
  options ->
  (options -> proof_differencer) -> (* diff f *)
  (options -> proof_differencer) -> (* diff each arg *)
  proof_differencer

(*
 * If the proofs are applications (f args) and (f' args'),
 * where f is an induction principle,
 * then recursively diff the functions and/or arguments.
 *
 * Use the options to determine how to combine the results.
 *)
val diff_app_ind :
  options ->
  (options -> ind_proof_differencer) -> (* diff f *)
  (options -> proof_differencer) -> (* diff each arg *)
  proof_differencer

(*
 * Difference an inductive proof.
 *
 * That is, break the proof into cases and difference each case separately.
 * In each case, abstract if necessary, then adjust the patch so it
 * type-checks in the original environment.
 *
 * Use the options to determine how to abstract and how much to adjust by.
 *)
val diff_inductive :
  options ->
  (options -> proof_differencer) ->
  (proof_cat * int) proof_diff ->
  candidates

(* --- Top-level differencer --- *)

(*
 * Given a configuration, return the appropriate top-level differencer
 *)
val get_differencer : options -> proof_differencer
