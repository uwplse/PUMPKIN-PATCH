(* Functions for inverting symmetric patches *)

open Term
open Environ

type inverter

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
