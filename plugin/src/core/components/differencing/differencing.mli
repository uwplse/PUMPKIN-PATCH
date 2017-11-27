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
  ind_proof_differencer

(* --- Top-level differencer --- *)

(*
 * Given a configuration, return the appropriate top-level differencer
 *)
val get_differencer : options -> proof_differencer
