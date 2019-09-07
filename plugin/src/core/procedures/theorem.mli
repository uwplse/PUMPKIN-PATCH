(* Updating theorems instead of proofs *)

open Constr
open Environ
open Evd
open Stateutils
       
(* 
 * Subtitute a term into a simple theorem
 * Try to update dependent types appropriately
 *)
val update_theorem : env -> types -> types -> types -> evar_map -> types state
