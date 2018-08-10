(* Strategies for reducing terms *)

open Environ
open Constr

type reducer = env -> types -> types

(* --- Top-level --- *)

val reduce_all : reducer -> env -> types list -> types list

(* --- Defaults --- *)

(*
 * Default reducer
 *)
val reduce_term : reducer

(* --- Custom reducers --- *)

(*
 * Do not reduce
 *)
val do_not_reduce : reducer

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
 * Reduce the body of a term using the supplied reducer if
 * the predicate p is true on the body. If the term is a function,
 * then this recurses into the body and checks the condition, and so on.
 * It reduces as soon as the condition holds.
 *)
val reduce_body_if : (env -> types -> bool) -> reducer -> reducer
