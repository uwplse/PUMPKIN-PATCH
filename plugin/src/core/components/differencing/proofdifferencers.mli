(* --- Differencing of Proofs --- *)

open Evd
open Searchopts
open Differencers

(*
 * Primitive differencing function
 *)
val find_difference : proof_differencer configurable

(*
 * Determine if two proof diffs are identical
 *)
val no_diff : proof_diff_predicate configurable

(*
 * Return the identity candidates applied to the type
 * of the new proof in the diff
 *)
val identity_candidates : proof_differencer
