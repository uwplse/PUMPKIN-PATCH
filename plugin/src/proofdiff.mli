(* Differences between old and new proofs *)

open Term
open Environ
open Proofcat
open Assumptions
open Expansion
open Substitution
open Reducers

(* --- Types --- *)

type 'a proof_diff
type 'a intro_strategy = 'a proof_diff -> 'a proof_diff option
type 'a zoomer =
  'a expansion_strategy ->
  'a intro_strategy ->
  'a proof_diff ->
  'a proof_diff option

(* Construct a proof_diff *)
val difference : 'a -> 'a -> equal_assumptions -> 'a proof_diff

(* Get the assumptions from a proof_diff *)
val assumptions : 'a proof_diff -> equal_assumptions

(* Get the old proof from a proof_diff *)
val old_proof : 'a proof_diff -> 'a

(* Get the new proof from a proof_diff *)
val new_proof : 'a proof_diff -> 'a

(* Change the assumptions of a proof_diff *)
val with_assumptions : equal_assumptions -> 'a proof_diff -> 'a proof_diff

(* Change the old proof of a proof_diff *)
val with_old_proof : 'a -> 'a proof_diff -> 'a proof_diff

(* Change the new proof of a proof_diff *)
val with_new_proof : 'a -> 'a proof_diff -> 'a proof_diff

(* --- Kinds of proof diffs --- *)

(* Difference between inductive proof_cats with params and leftover arguments *)
type induction_diff = (proof_cat * int * (types list)) proof_diff

(* Non-contextual difference between two proof categories *)
type proof_cat_diff = proof_cat proof_diff

(* Difference between two proof categories that have been split into cases *)
type case_diff = (proof_cat list) proof_diff

(* Difference between two goal contexts without any proof information *)
type lift_goal_diff = context_object proof_diff
type lift_goal_type_diff = (types * env) proof_diff

(* Difference between two terms given their types *)
type 'a term_diff = ('a * types) proof_diff

(* Difference between two terms given a (type, env) goal *)
type goal_type_term_diff = (types * env) term_diff

(* Difference between two terms with a goal context *)
type 'a goal_diff = (context_object * 'a) proof_diff
type goal_term_diff = types goal_diff
type goal_proof_diff = proof_cat goal_diff
type goal_case_diff = (arrow list) goal_diff

(* --- Construction and destruction --- *)

(* Get the proof terms for a goal_diff *)
val diff_proofs : 'a goal_diff -> 'a * 'a

(* Get the proof terms for a proof diff *)
val proof_terms : goal_proof_diff -> (types * types)

(* Get the reduced proof terms for a proof diff *)
val reduced_proof_terms : reducer -> goal_proof_diff -> env * types * types

(* Get the goal types for a lift goal diff *)
val goal_types : lift_goal_diff -> (types * types)

(* --- Transformations between proof diffs --- *)

(* Map a function on the old and new proofs of a diff and update assumptions *)
val map_diffs :
  ('a -> 'b) ->
  (equal_assumptions -> equal_assumptions) ->
  'a proof_diff ->
  'b proof_diff

(*
 * Add extra information to the old and new proofs, respectively
 *)
val add_to_diff : 'a proof_diff -> 'b -> 'b -> ('a * 'b) proof_diff

(*
 * Reverse a diff, so that the new proof is the old proof and the
 * old proof is the new proof.
 *)
val reverse : 'a proof_diff -> 'a proof_diff

(*
 * Swap the goals in a goal diff
 *)
val swap_goals : 'a goal_diff -> 'a goal_diff

(*
 * Given a difference in proof categories, get the contexts for the
 * types of the conclusions, and return
 * a new difference that includes these as goal types
 *)
val add_goals : proof_cat_diff -> goal_proof_diff

(*
 * Erase the goals; go in the opposite direction of above
 *)
val erase_goals : 'a goal_diff -> 'a proof_diff

(*
 * Erase the proof terms, however they are represented, from a goal_diff
 *)
val erase_proofs : 'a goal_diff -> lift_goal_diff

(*
 * Convert a difference in proof categories to a difference in terms
 *)
val proof_to_term : goal_proof_diff -> goal_term_diff


(*
 * Retain the same goals and assumptions, but update the old proof
 * with a term in a goal proof diff
 *)
val eval_with_old_term : types -> goal_proof_diff -> goal_proof_diff

(*
 * Retain the same goals and assumptions, but update the new proof
 * with a term in a goal proof diff
 *)
val eval_with_new_term : types -> goal_proof_diff -> goal_proof_diff

(*
 * Retain the same goals and assumptions, but update the old and new
 * terms with the terms in a goal proof diff
 *)
val eval_with_terms : types -> types -> goal_proof_diff -> goal_proof_diff

(*
 * Destruct the contexts in a goal_diff and return a new diff
 *)
val dest_goals : 'a goal_diff ->  ((types * env) * 'a) proof_diff

(*
 * Destruct the contexts in a lift_goal_diff and return a new diff
 *)
val dest_lift_goals : lift_goal_diff -> lift_goal_type_diff

(*
 * Destruct a case diff into a list of diffs, one for each case
 *)
val dest_cases : case_diff -> proof_cat_diff list

(* --- Merging environments for diffs --- *)

(*
 * Merge the environments for two lift_goal_type_diffs
 * Combine with a list of terms in the old environment
 * Return them in the order (env, new, old ++ terms)
 *)
val merge_lift_diff_closures :
  lift_goal_type_diff -> types list -> merged_closure

(*
 * Merge the environments for two goal_type_term_diffs
 * Combine with a list of terms in the old environment
 * Return them in the order (env, new, old ++ terms)
 *)
val merge_diff_closures :
  goal_type_term_diff -> types list -> merged_closure

(* --- Reduction --- *)

(* Reduce the terms inside of a goal_proof_diff *)
val reduce_diff : reducer -> goal_proof_diff -> goal_proof_diff

(* --- Questions about a difference between proofs --- *)

(*
 * Check if two types are inductive types with the same shape
 * That is, they have the same number of constructors
 * And (temporarily) only one constructor has changed
 *
 * Fail if there are any assumptions in d
 *)
val same_shape : env -> types proof_diff -> bool

(*
 * Given two inductive types with the same shape,
 * return the difference between them
 *
 * Fail if they are not the same shape
 *)
val ind_type_diff : env -> types proof_diff -> types proof_diff

(*
 * Check whether two proof categories for inductive proofs
 * induct over the same hypothesis.
 *
 * Uses the supplied function to check if two terms are the same
 *
 * This expects both proof categories not to be expanded.
 * It will error if the proof is already expanded.
 *)
val induct_over_same_h : (types -> types -> bool) -> goal_proof_diff -> bool

(* --- Zooming --- *)

(*
 * Zooming is what we call an operation that involves:
 * 1. (Possibly) expanding both proof categories
 * 2. (Possibly) removing premises from the proof categories
 * 3. (Possibly) shifting the assumptions appropriately
 *
 * Zooming takes an expansion strategy and an introduction strategy.
 * When we introduce common elements, we assume they are equal.
 * Otherwise, we shift the assumptions each time we introduce
 * a non-common assumptions, since the initial environment is different.
 *
 * Zooming can internally reference evaluation.
 * When we zoom over inductive types with the same hypotheses, for example,
 * we evaluate the induction principle internally and evaluate the proof
 * category into an inductive proof category. The common idea is
 * that it will transform both arguments in the difference into
 * something that makes search easier and reveals more information,
 * then possibly return leftover arguments that are helpful.
 *
 * We do not zoom when we have only one morphism left,
 * since doing so would remove the proof.
 *
 * We do not zoom when we have no morphisms left,
 * since that is not possible.
 *)

(*
 * Introduce a common element of two categories if possible
 * Remove that element from the premise of both
 * Add it to the assumptions
 *)
val intro_common : proof_cat intro_strategy

(*
 * Introduce n common elements of two categories if possible
 * Remove those elements from the premise of both
 * Add them to the assumptions
 *)
val intro_common_n : int -> proof_cat intro_strategy

(*
 * Introduce an element of two categories if possible
 * Remove it from the premise of c1 and c2
 * Shift the assumptions
 *)
val intro : proof_cat intro_strategy

(*
 * Introduce n elements of two cateogries if possible
 * Remove those elements from the premise of both
 * Shift the assumptions
 *)
val intro_n : int -> proof_cat intro_strategy

(* Zoom *)
val zoom : 'a zoomer

(*
 * Zoom
 * If it was successful, apply the function to the result
 * Otherwise, default to a default element
 *)
val zoom_map :
  ('a proof_diff -> 'b) ->
  'b ->
  'a expansion_strategy ->
  'a intro_strategy ->
  'a proof_diff ->
  'b

(*
 * Zoom over two inductive proofs that induct over the same hypothesis
 * Return the leftover arguments that aren't applied to the inductive type
 *)
val zoom_same_hypos : induction_diff -> induction_diff option
