(* Higher-order functions on terms *)

open Environ
open Constr
open Coqterms

(* Predicates to determine whether to apply a mapped function *)
type ('a, 'b) pred = 'a -> 'b -> bool
type ('a, 'b) pred_with_env = env -> ('a, 'b) pred

(* Functions to use in maps *)
type ('a, 'b) transformer = 'a -> 'b -> 'b
type ('a, 'b) cartesian_transformer = 'a -> 'b -> 'b list
type ('a, 'b) transformer_with_env = env -> 'a -> 'b -> 'b
type ('a, 'b) cartesian_transformer_with_env = env -> 'a -> 'b -> 'b list

(* Updating arguments *)
type 'a updater = 'a -> 'a

(* Mapper functions *)
type ('a, 'b) mapper_with_env =
  ('a, 'b) transformer_with_env ->
  'a updater ->
  ('a, 'b) transformer_with_env

type ('a, 'b) mapper =
  ('a, 'b) transformer ->
  'a updater ->
  ('a, 'b) transformer

type ('a, 'b) cartesian_mapper_with_env =
  ('a, 'b) cartesian_transformer_with_env ->
  'a updater ->
  ('a, 'b) cartesian_transformer_with_env

type ('a, 'b) cartesian_mapper =
  ('a, 'b) cartesian_transformer ->
  'a updater ->
  ('a, 'b) cartesian_transformer

type ('a, 'b) conditional_mapper_with_env =
  ('a, 'b) pred_with_env ->
  ('a, 'b) transformer_with_env ->
  'a updater ->
  ('a, 'b) transformer_with_env

type ('a, 'b) conditional_mapper =
  ('a, 'b) pred ->
  ('a, 'b) transformer ->
  'a updater ->
  ('a, 'b) transformer

type ('a, 'b) conditional_cartesian_mapper_with_env =
  ('a, 'b) pred_with_env ->
  ('a, 'b) cartesian_transformer_with_env ->
  'a updater ->
  ('a, 'b) cartesian_transformer_with_env

(* --- Terms --- *)

(*
 * Map a function over a term in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term_env : ('a, types) mapper_with_env

(*
 * Map a function over a term, when the environment doesn't matter
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term : ('a, types) mapper

(*
 * Map a function over subterms of a term in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
val map_subterms_env : ('a, types) cartesian_mapper_with_env

(*
 * Map a function over subterms of a term, when the environment doesn't matter
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
val map_subterms : ('a, types) cartesian_mapper

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term_env_if : ('a, types) conditional_mapper_with_env

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Don't recurse into lambda arguments
 * Return a new term
 *)
val map_term_env_if_shallow : ('a, types) conditional_mapper_with_env

(*
 * Map a function over a term where the environment doesn't matter
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term_if : ('a, types) conditional_mapper

(*
 * Map a function over subterms of a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
val map_subterms_env_if : ('a, types) conditional_cartesian_mapper_with_env

(*
 * Map a function over subterms of a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly, but always recurse
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
val map_subterms_env_if_combs : ('a, types) conditional_cartesian_mapper_with_env

(*
 * Map a function over subterms of a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function after recursing
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
val map_subterms_env_if_lazy : ('a, types) conditional_cartesian_mapper_with_env
