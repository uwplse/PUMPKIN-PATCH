open Proofdiff
open Environ
open Expansion
open Proofcat
open Candidates
open Names
open Constr
open Stateutils
open Evd
open Assumptions

(* --- Zooming --- *)

type search_function = proof_cat_diff -> evar_map -> candidates state
type 'a intro_strategy = 'a proof_diff -> evar_map -> ('a proof_diff option) state

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
  evar_map ->
  ('a proof_diff option) state

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
  ('a proof_diff -> evar_map -> 'b state) ->
  'b ->
  'a expansion_strategy ->
  'a intro_strategy ->
  'a proof_diff ->
  evar_map ->
  'b state

(*
 * Default zoom for recursive search
 *)
val zoom_search : search_function -> goal_proof_diff -> evar_map -> candidates state

(*
 * Zoom in, search, and wrap the result in a lambda
 *)
val zoom_wrap_lambda :
  search_function ->
  Name.t ->
  types ->
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state

(*
 * Zoom in, search, and wrap the result in a product
 *)
val zoom_wrap_prod :
  search_function -> Name.t -> types -> goal_proof_diff -> evar_map -> candidates state

(*
 * Zoom in, search, and unshift the result
 *)
val zoom_unshift :
  search_function ->
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state

