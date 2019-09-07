(* Differences between old and new proofs *)

open Constr
open Environ
open Proofcat
open Assumptions
open Reducers
open Merging
open Stateutils
open Evd

(* --- Types --- *)

type 'a proof_diff

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

(* Get the goal types for a lift goal diff *)
val goal_types : lift_goal_diff -> (types * types)

(* --- Transformations between proof diffs --- *)

(* Map a function on the old and new proofs of a diff and update assumptions *)
val map_diffs :
  ('a -> evar_map -> 'b state) ->
  (equal_assumptions -> evar_map -> equal_assumptions state) ->
  'a proof_diff ->
  evar_map ->
  'b proof_diff state

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
val eval_with_old_term : types -> goal_proof_diff -> evar_map -> goal_proof_diff state

(*
 * Retain the same goals and assumptions, but update the new proof
 * with a term in a goal proof diff
 *)
val eval_with_new_term : types -> goal_proof_diff -> evar_map -> goal_proof_diff state

(*
 * Retain the same goals and assumptions, but update the old and new
 * terms with the terms in a goal proof diff
 *)
val eval_with_terms : types -> types -> goal_proof_diff -> evar_map -> goal_proof_diff state

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

(*
 * Expand constructors in a proof_cat_diff
 *)
val expand_constrs : proof_cat_diff -> evar_map -> proof_cat_diff state

(* --- Merging environments for diffs --- *)

(*
 * Merge the environments for two lift_goal_diffs
 * Combine with a list of terms in the old environment
 * Return (env, types diff, terms)
 *)
val merge_lift_diff_envs :
  lift_goal_diff -> types list -> (env * types proof_diff * types list)

(*
 * Merge the environments for two goal_type_term_diffs
 * Combine with a list of terms in the old environment
 * Return them in the order (env, new, old ++ terms)
 *)
val merge_diff_closures :
  goal_type_term_diff -> types list -> merged_closure

(* --- Reduction and Simplification --- *)

(* Reduce the terms inside of a goal_proof_diff *)
val reduce_diff : reducer -> goal_proof_diff -> evar_map -> goal_proof_diff state

(* Given a difference in proofs, trim down any casts and get the terms *)
val reduce_casts : goal_proof_diff -> evar_map -> goal_proof_diff state

(*
 * Given a differrence in proofs, weak head reduce any let-ins
 * If this fails because of a substituted assumption, then fail silently
 *)
val reduce_letin : goal_proof_diff -> evar_map -> goal_proof_diff state

(* Given a difference in proofs, trim applications of the IH *)
val reduce_trim_ihs : goal_proof_diff -> evar_map -> goal_proof_diff state

(* --- Assumptions --- *)

(*
 * Update the assumptions in the difference between a case of an inductive proof
 * Assume terms are equal when they are convertible, and offset accordingly
 *)
val update_case_assums : (arrow list) proof_diff -> evar_map -> equal_assumptions state

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

(*
 * Given a function that extracts an environment from a proof,
 * get the number of bindings that are not common to both proofs.
 *)
val num_new_bindings : ('a -> env) -> 'a proof_diff -> int
