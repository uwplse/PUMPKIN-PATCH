(* Updating theorems instead of proofs *)

open Term
open Environ

(* 
 * Subtitute a term into a simple theorem
 * Try to update dependent types appropriately
 *)
val update_theorem : env -> types -> types -> types -> types
