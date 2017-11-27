(* --- Differencing of Fixpoints --- *)

open Coqenvs
open Differencers

(*
 * Find the difference between the cases of two fixpoints
 *
 * This operates at the term level, since compilation currently
 * doesn't model fixpoints.
 *)
val diff_fix_cases : term_differencer contextual
