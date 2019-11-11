(* --- Differencing of Fixpoints --- *)

open Environ
open Differencers
open Evd
open Constr

(*
 * Find the difference between the cases of two fixpoints
 *
 * This operates at the term level, since compilation currently
 * doesn't model fixpoints.
 *)
val diff_fix_cases : env -> constr candidate_differencer
