(* DeBruijn management *)

open Environ
open Term

(* --- Indexes --- *)

(* Unshift an index by a given amount *)
val unshift_i_by : int -> int -> int

(* Shift an index by a given amount *)
val shift_i_by : int -> int -> int

(* Unshift an index *)
val unshift_i : int -> int

(* Shift an index *)
val shift_i : int -> int

(* --- Terms --- *)

(*
 * Unshifts a term by an amount if it is greater than the maximum index
 * of a local binding
 *)
val unshift_local : int -> int -> types -> types

(*
 * Shifts a term by an amount if it is greater than the maximum index
 * of a local binding
 *)
val shift_local : int -> int -> types -> types

(* Decrement the relative indexes of a term by an amount *)
val unshift_by : int -> types -> types

(* Increment the relative indexes of a term by an amount *)
val shift_by : int -> types -> types

(* Increment the relative indexes of a term by one *)
val shift : types -> types

(* Decrement the relative indexes of a term by one *)
val unshift : types -> types

(* Shift everything and pray; workaround for bug *)
val shift_by_unconditional : int -> types -> types

(* --- Environments --- *)

(* Unshifts indexes for terms in an environment by an amount *)
val unshift_env_by : int -> env -> env

