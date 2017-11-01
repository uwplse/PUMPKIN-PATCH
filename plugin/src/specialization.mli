(* --- Specialization Component --- *)

open Term
open Environ

(*
 * Specialize an applied function by its arguments.
 *
 * If the term does not have one of these forms:
 * 1) f args
 * 2) (fun ... => f args)
 * then this will fail.
 *)
val specialize_application : env -> types -> types
