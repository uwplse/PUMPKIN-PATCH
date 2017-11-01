(* --- Specialization Component --- *)

(*
 * The default approach (specialize_using specialize_term)
 * is function application followed by betaiota reduction.
 *
 * We expose more advanced specialization approaches so that it is
 * easy to customize how this is called, which is useful
 * for future extension to the tool.
 *)

open Term
open Environ

(*
 * A reducer specializes within a term.
 * A specializer specializes explicitly to some arguments.
 *)

type reducer
type specializer

(* --- Top-level --- *)

val specialize_using : specializer -> env -> types -> types array -> types
val reduce_using : reducer -> env -> types -> types
val reduce_all : reducer -> env -> types list -> types list

(* --- Defaults --- *)

(*
 * Default specializer
 *)
val specialize_term : specializer

(*
 * Default reducer
 *)
val reduce_term : reducer

(* --- Custom reducers --- *)

(*
 * Remove all applications of the identity function
 *)
val remove_identities : reducer

(*
 * Remove unused hypotheses
 *)
val remove_unused_hypos : reducer

(*
 * Remove all applications of the identity function, then default reduce
 *)
val reduce_remove_identities : reducer

(*
 * Default reduce and also unfold definitions (delta-reduce, nf)
 *)
val reduce_unfold : reducer

(*
 * Default reduce and also unfold definitions (delta-reduce, whd)
 *)
val reduce_unfold_whd : reducer

(*
 * Weak-head reduce a term if it is a let-in (conditional betaiotazeta, whd)
 *)
val reduce_whd_if_let_in : reducer

(* --- Combinators and converters --- *)

(*
 * Reduce with the first reducer, then with the second reducer
 *)
val chain_reduce : reducer -> reducer -> reducer

(*
 * Try to reduce, but let failure be OK
 *)
val try_reduce : reducer -> reducer

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

(*
 * Convert a reducer into a specializer in the obvious way
 *)
val reducer_to_specializer : reducer -> specializer
