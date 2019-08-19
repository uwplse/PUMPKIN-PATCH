(* Equality assumptions for substitutions in proof search *)

open Constr
open Environ
open Evd
open Stateutils

type equal_assumptions
type param_substitutions
type swap_map

val no_assumptions : equal_assumptions
val no_substitutions : param_substitutions
val no_swaps : swap_map

(* --- Auxiliary functions on assumptions --- *)

(* Print a list of substitutions for debugging purposes *)
val substitutions_as_string : env -> param_substitutions -> string

(* Is there an assumption about the term? *)
val has_assumption : equal_assumptions -> types -> bool

(* Is there a substitution from the provided term? *)
val has_substitution : param_substitutions -> types -> bool

(*
 * Get the assumption about the term
 * Fail if has_assumption is false
 *)
val get_assumption : equal_assumptions -> types -> types

(*
 * Get the substitution for a parameter
 * Fail if has_substitution is false
 *)
val get_substitution : param_substitutions -> types -> types

(* Get the number of assumptions *)
val num_assumptions : equal_assumptions -> int

(* Assume equality of all terms not in the assumptions of the source env *)
val complement_assumptions : equal_assumptions -> env -> equal_assumptions

(* Split assumptions into the original assumptions and the complement *)
val split_assumptions : equal_assumptions -> env -> (equal_assumptions * equal_assumptions)

(* Take the union of two sets of assumptions *)
val union_assumptions : equal_assumptions -> equal_assumptions -> equal_assumptions

(* Reverse assumptions *)
val reverse_assumptions : equal_assumptions -> equal_assumptions

(* --- DeBruijn operations for assumptions --- *)

(* Unshift all assumptions by an amount *)
val unshift_assumptions_by : int -> equal_assumptions -> equal_assumptions

(* Unshift all substitutions by an amount *)
val unshift_substitutions_by : int -> param_substitutions -> param_substitutions

(* Shift all assumptions by an amount *)
val shift_assumptions_by : int -> equal_assumptions -> equal_assumptions

(* Shift all substitutions by an amount *)
val shift_substitutions_by : int -> param_substitutions -> param_substitutions

(* Hack *)
val shift_substitutions_by_uncoditional : int -> param_substitutions -> param_substitutions

(* Unshift all assumption sources by an amount *)
val unshift_from_assumptions_by : int -> equal_assumptions -> equal_assumptions

(* Unshift all substitution sources by an amount *)
val unshift_from_substitutions_by : int -> param_substitutions -> param_substitutions

(* Shift all assumption sources by an amount *)
val shift_from_assumptions_by : int -> equal_assumptions -> equal_assumptions

(* Shift all substitution sources by an amount *)
val shift_from_substitutions_by : int -> param_substitutions -> param_substitutions

(* Unshift all assumption destinations by an amount *)
val unshift_to_assumptions_by : int -> equal_assumptions -> equal_assumptions

(* Unshift all substitution destinations by an amount *)
val unshift_to_substitutions_by : int -> param_substitutions -> param_substitutions

(* Shift all assumption destinations by an amount *)
val shift_to_assumptions_by : int -> equal_assumptions -> equal_assumptions

(* Shift all substitution destinations by an amount *)
val shift_to_substitutions_by : int -> param_substitutions -> param_substitutions

(* Unshift all assumptions *)
val unshift_assumptions : equal_assumptions -> equal_assumptions

(* Shift all assumptions *)
val shift_assumptions : equal_assumptions -> equal_assumptions

(* Shift all substitutions *)
val shift_substitutions : param_substitutions -> param_substitutions

(* Unshift all assumption sources *)
val unshift_from_assumptions : equal_assumptions -> equal_assumptions

(* Shift all assumption sources *)
val shift_from_assumptions : equal_assumptions -> equal_assumptions

(* Unshift all assumption destinations *)
val unshift_to_assumptions : equal_assumptions -> equal_assumptions

(* Shift all assumption destinations *)
val shift_to_assumptions : equal_assumptions -> equal_assumptions

(* --- Making new assumptions --- *)

(* Assume that the n closest local bindings are equal in both envs *)
val assume_local_n_equal : int -> equal_assumptions -> equal_assumptions

(*
 * Build substitutions for the n closest local bindings to a list of n terms
 * Fail if the list of terms is not length n
 *)
val build_n_substitutions : int -> types list -> param_substitutions -> param_substitutions

(* Assume that the closest local bindings are equal in both envs *)
val assume_local_equal : equal_assumptions -> equal_assumptions

(* Build a substitution for the closest local binding to a term *)
val build_substitution : types -> param_substitutions -> param_substitutions

(* --- Applying assumptions --- *)

(*
 * Apply a set of assumptions within a term
 *)
val substitute_assumptions : equal_assumptions -> types -> types

(*
 * Substitute in values for parameters for an inductive type
 *)
val substitute_params : param_substitutions -> types -> types

(*
 * Substitute in values for parameters for an inductive type in an environment
 *)
val substitute_env_params : param_substitutions -> env -> env

(* --- Auxiliary functions on swaps --- *)

(*
 * Given a swap map, make a unique swap map (no repeats and only one direction)
 *)
val unique_swaps : swap_map -> swap_map

(*
 * Filter a swap map by a relation on a pair of types
 *)
val filter_swaps :
  ((types * types) -> evar_map -> bool state) ->
  swap_map ->
  evar_map ->
  swap_map state

(*
 * Map a function on two types along a swap map and return a list
 *)
val map_swaps : ((types * types) -> 'a) -> swap_map -> 'a list

(*
 * Flatten a list of swap maps into one swap map with no duplicates
 *)
val merge_swaps : swap_map list -> swap_map

(*
 * Build a swap map from two arrays of arguments
 *)
val of_arguments : types array -> types array -> swap_map

(*
 * Build a swap map for all combinations of an array of arguments
 *)
val combinations_of_arguments : types array -> swap_map

(*
 * Unshift a swap map by n
 *)
val unshift_swaps_by : int -> swap_map -> swap_map

(*
 * Shift a swap map by n
 *)
val shift_swaps_by : int -> swap_map -> swap_map

(*
 * Unshift a swap map
 *)
val unshift_swaps : swap_map -> swap_map

(*
 * Shift a swap map
 *)
val shift_swaps : swap_map -> swap_map

(* --- Applying swaps --- *)

(*
 * In an environment, swaps all subterms  convertible to the source
 * and destination terms in the swap map with each other.
 *
 * This checks convertibility after recursing, and so will replace at
 * the lowest level possible.
 *)
val all_conv_swaps_combs :
  env -> swap_map -> types -> evar_map -> (types list) state

(*
 * In an environment, swaps all subterms with types convertible to the source
 * and destination types with each other.
 *
 * This checks convertibility after recursing, and so will replace at
 * the lowest level possible.
 *)
val all_typ_swaps_combs : env -> types -> evar_map -> (types list) state
