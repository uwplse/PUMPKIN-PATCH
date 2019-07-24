open Proofdiff
open Environ
open Expansion
open Proofcat
open Candidates
open Names
open Constr

(* --- Zooming --- *)

type search_function = proof_cat_diff -> candidates
type 'a intro_strategy = 'a proof_diff -> 'a proof_diff option

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

type 'a zoomer =
  'a expansion_strategy ->
  'a intro_strategy ->
  'a proof_diff ->
  'a proof_diff option

(* --- Introduction strategies --- *)

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

(*
 * Introduce the provided number of parameters to an inductive diff
 * Fail if both proofs do not have the same number of parameters
 *)
val intro_params : int -> proof_cat intro_strategy

(* --- Zoomers and applying them --- *)

(*
 * Zoom
 *)
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

(*
 * Default zoom for recursive search
 *)
val zoom_search : search_function -> goal_proof_diff -> candidates

(*
 * Zoom in, search, and wrap the result in a lambda
 *)
val zoom_wrap_lambda :
  search_function -> Name.t -> types -> goal_proof_diff -> candidates

(*
 * Zoom in, search, and wrap the result in a product
 *)
val zoom_wrap_prod :
  search_function -> Name.t -> types -> goal_proof_diff -> candidates

(*
 * Zoom in, search, and unshift the result
 *)
val zoom_unshift : search_function -> goal_proof_diff -> candidates

