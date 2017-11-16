(* --- Inversion Component --- *)

open Term
open Environ

type inverter

(*
 * Try to invert a single factor
 * Try both exploiting type symmetry (as in eq_ind), and also
 * strategically swapping arguments with convertible types
 *)
val invert_factor : inverter

(*
 * Try to invert a list of terms in an environment
 * Recursively invert function composition
 * Use the supplied inverter to handle low-level inverses
 *)
val invert_terms : inverter -> env -> types list -> types list
