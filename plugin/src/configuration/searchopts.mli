(* Search configuration *)

open Constr
open Proofdiff
open Cutlemma
open Kindofchange
open Candidates
open Catzooming
open Evd
open Stateutils
open Proofcat
open Environ
open Assumptions

(* --- Options for search --- *)

type options
type 'a configurable = options -> 'a

(* --- Configuring options --- *)

(* Build configuration options for the search *)
val configure_search :
  kind_of_change ->
  cut_lemma option ->
  options

(* --- Modifying options --- *)

(* Set the inductive case flag *)
val set_is_ind : options -> bool -> options

(* Set the kind of change *)
val set_change : options -> kind_of_change -> options

(* --- Using options --- *)

(* Update the goals of search *)
val update_search_goals :
  ((env * env) ->
   (constr * constr) ->
   (types * types) ->
   (env * env) ->
   (constr * constr) ->
   evar_map ->
   ((env * env) * (constr * constr) * (types * types)) state) configurable

(* Swap the goals of search *)
val swap_search_proofs : ((constr * constr) -> (constr * constr)) configurable

(* Reset the goals of search for an inductive case *)
val reset_case_goals :
  (goal_proof_diff -> goal_case_diff -> goal_case_diff) configurable

(* Determine whether two terms induct over the same hypothesis *)
val same_h : (env -> types -> types -> evar_map -> bool state) configurable

(*
 * Determine whether one term applies the other
 *
 * This function has a sense of direction, and the direction is determined
 * by the kind of change
 *)
val is_app : (goal_proof_diff -> bool) configurable

(* Get the kind of change *)
val get_change : kind_of_change configurable

(* Determine whether we are in the inductive case of search *)
val is_ind : bool configurable

(*
 * Convert a search function that takes a set of options to a
 * search_function that is independent of options, which
 * can be used by zooming.
 *)
val to_search_function :
  ((goal_proof_diff -> evar_map -> candidates state) configurable) ->
  (goal_proof_diff -> search_function) configurable

(*
 * Check if the proofs apply the inductive hypothesis
 *)
val applies_ih :
  (goal_proof_diff -> bool) configurable
