(* --- Differencing of Proofs --- *)

open Searchopts
open Differencers

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
