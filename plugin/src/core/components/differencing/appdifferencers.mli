open Searchopts
open Differencers

(* --- Recursive Differencers for Application --- *)

(*
 * If the proofs are applications (f args) and (f' args'),
 * then recursively diff the functions and/or arguments.
 *
 * Use the options to determine how to combine the results.
 *)
val diff_app :
  proof_differencer configurable -> (* diff f *)
  proof_differencer configurable -> (* diff each arg *)
  proof_differencer configurable

(*
 * If the proofs are applications (f args) and (f' args'),
 * where f is an induction principle,
 * then recursively diff the functions and/or arguments.
 *
 * Use the options to determine how to combine the results.
 *)
val diff_app_ind :
  ind_proof_differencer configurable -> (* diff f *)
  proof_differencer configurable -> (* diff each arg *)
  proof_differencer configurable

