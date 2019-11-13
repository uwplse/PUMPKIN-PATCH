open Environ
open Constr
open Evd
open Stateutils

(*
 * Refactoring functionality
 *)

(*
 * Find all subterms of the second term convertible with the first term,
 * and replace all of those with the first term itself
 *
 * Optionally, also generate correctness proof
 *)
val replace_all_convertible :
  bool ->
  env ->
  constr ->
  constr ->
  evar_map ->
  (constr * (constr * constr) option) state
