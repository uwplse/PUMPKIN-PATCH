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
 *)
val replace_all_convertible :
  env -> constr -> constr -> evar_map -> constr state
