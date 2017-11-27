(* --- Differencing Component --- *)

open Proofcat
open Searchopts
open Proofdiff
open Candidates
open Environ
open Term
open Cutlemma
open Differencers

(* TODO clean above when done refactoring *)

(* --- Differencing of types & terms --- *)

(*
 * Find the difference between the cases of two fixpoints
 *)
val diff_fix_cases : env -> term_differencer

(* --- Top-level differencer --- *)

(*
 * Given a configuration, return the appropriate top-level differencer
 *)
val get_differencer : proof_differencer configurable
