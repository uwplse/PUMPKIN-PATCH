(* --- Differencing Component --- *)

open Searchopts
open Proofdiff
open Abstracters

(*
 * Primitive differencing function
 *)
val find_difference : options -> goal_term_diff -> candidates

(*
 * Determine if two proof diffs are identical
 *)
val no_diff : options -> goal_proof_diff -> bool
