(* --- Specialization Component --- *)

(*
 * The default approach (specialize_using specialize_term)
 * is function application followed by betaiota reduction.
 *
 * We expose more advanced specialization approaches so that it is
 * easy to customize how this is called, which is useful
 * for future extension to the tool.
 *)

open Constr
open Environ
open Evd
open Reducers
open Stateutils

(*
 * A reducer specializes within a term.
 * A specializer specializes explicitly to some arguments.
 *)

type specializer

(* --- Top-level --- *)

val specialize_using :
  specializer -> env -> types -> types array -> evar_map -> types state

(* --- Defaults --- *)

(*
 * Default specializer
 *)
val specialize_term : specializer

(* --- Custom specializers --- *)

(*
 * Specialize without reduction (so just apply function)
 *)
val specialize_no_reduce : specializer

(* --- Conversion between specializers and reducers --- *)

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
