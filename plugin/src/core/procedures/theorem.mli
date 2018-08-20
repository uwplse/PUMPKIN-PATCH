(* Updating theorems instead of proofs *)

open Constr
open Environ
open Evd

(* 
 * Subtitute a term into a simple theorem
 * Try to update dependent types appropriately
 *)
val update_theorem : env -> evar_map -> types -> types -> types -> types
