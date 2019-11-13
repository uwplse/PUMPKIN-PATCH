open Environ
open Constr
open Evd
open Stateutils

(*
 * Refactoring functionality
 *)

(*
 * Find all subterms of the second term convertible with anything in the list of * the first terms, and replace all of those with the appropriate element from
 * the list itself. Do the replacements from left to right in the list.
 *
 * Optionally, also generate correctness proof.
 *)
val replace_all_convertible :
  bool ->
  env ->
  constr list ->
  constr ->
  evar_map ->
  (constr * (constr * constr) option) state
