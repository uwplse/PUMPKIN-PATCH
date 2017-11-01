(* --- Specialization Component --- *)

open Term
open Environ

(*
 * A reducer specializes within a term.
 * A specializer specializes explicitly to some arguments.
 *)

type reducer
type specializer

(* --- Specializers --- *)

(* Specialize a term by some arguments, default approach *)
val specialize_term : specializer

(* --- Reducers --- *)

(*
 * Specialize an applied function in a term body by its arguments.
 *
 * If the term does not have one of these forms:
 * 1) f args
 * 2) (fun ... => f args)
 * then this will fail.
 *)
val specialize_body : specializer -> reducer

(*
 * Specialize the body of a term using the supplied specializer if
 * the predicate p is true on the body. If the term is a function,
 * then this recurses into the body and checks the condition, and so on.
 * It specializes as soon as the condition holds.
 *)
val reduce_body_if : (env -> types -> bool) -> reducer -> reducer

(*
 * Convert a specializer into a reducer by taking arguments
 *)
val specialize_to : types array -> specializer -> reducer

(*
 * Convert a specializer into a reducer by taking the function
 * This only handles a single argument
 *)
val specialize_in : types -> specializer -> reducer

(* --- Top-level --- *)

val specialize_using : specializer -> env -> types -> types array -> types
val reduce_using : reducer -> env -> types -> types

