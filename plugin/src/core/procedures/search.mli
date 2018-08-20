(* Search procedures *)

open Constr
open Proofdiff
open Searchopts
open Environ
open Evd

(*
 * Search for a patch given a default patch and a difference in proof cats
 * Return the default patch if we cannot find a patch
 * Otherwise, return any patch we can find
 *)
val search_for_patch : types -> options -> env -> evar_map -> types proof_diff -> types

