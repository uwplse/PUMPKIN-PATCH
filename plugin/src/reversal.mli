(* Functions for inverting symmetric patches *)

open Term
open Environ

type inverter
type factors = (env * types) list

(*
 * Given a term, if the term is a function with type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F)
 *)
val factor_term : env -> types -> factors

(*
 * Try to invert a single simple patch
 * Try both exploiting type symmetry (as in eq_ind), and also
 * strategically swapping arguments with convertible types
 *)
val invert_patch : inverter

(*
 * Try to invert a list of terms in an environment
 * Recursively invert function composition
 * Use the supplied inverter to handle low-level inverses
 *)
val invert_patches : inverter -> env -> types list -> types list
