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
