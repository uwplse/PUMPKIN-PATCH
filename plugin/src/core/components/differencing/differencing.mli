(* --- Differencing Component --- *)

open Proofcat
open Searchopts
open Proofdiff
open Candidates
open Environ
open Term
open Cutlemma
open Kindofchange

type ('a, 'b) differencer = 'a proof_diff -> 'b

type 'a candidate_differencer = ('a, candidates) differencer
type proof_differencer = (context_object * proof_cat) candidate_differencer
type term_differencer = types candidate_differencer
type flat_args_differencer = (types array) candidate_differencer
type ind_proof_differencer = (proof_cat * int) candidate_differencer

type 'a candidate_list_differencer = ('a, candidates list) differencer
type args_differencer = (types array) candidate_list_differencer

type 'a change_detector = ('a, kind_of_change) differencer
type proof_change_detector = (context_object * proof_cat) change_detector

type 'a predicate_differencer = ('a, bool) differencer
type proof_diff_predicate = (context_object * proof_cat) predicate_differencer

(* --- Differencing of types & terms --- *)

(*
 * Find the difference between the cases of two fixpoints
 *)
val diff_fix_cases : env -> term_differencer

(* --- Differencing of proofs --- *)

(*
 * Given a difference in proofs with goals and an optional lemma to cut by,
 * determine what has changed about the proof
 *)
val find_kind_of_change : cut_lemma option -> proof_change_detector

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
