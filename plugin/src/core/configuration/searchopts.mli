(* Search configuration *)

open Term
open Environ
open Proofdiff
open Cutlemma
open Kindofchange
open Candidates
open Zooming

(* --- Options for search --- *)

type options

(* --- Configuring options --- *)

(* Build configuration options for the search *)
val configure_search :
  goal_proof_diff -> kind_of_change -> cut_lemma option -> options

(* --- Modifying options --- *)

(* Set the inductive case flag *)
val set_is_ind : options -> bool -> options

(* Set the kind of change *)
val set_change : options -> kind_of_change -> options

(* --- Using options --- *)

(* Update the goals of search *)
val update_search_goals :
  options -> goal_proof_diff -> proof_cat_diff -> goal_proof_diff

(* Swap the goals of search *)
val swap_search_goals : options -> goal_term_diff -> goal_term_diff

(* Reset the goals of search for an inductive case *)
val reset_case_goals : options -> goal_case_diff -> goal_case_diff

(* Determine whether two terms induct over the same hypothesis *)
val same_h : options -> types -> types -> bool

(*
 * Determine whether one term applies the other
 *
 * This function has a sense of direction, and the direction is determined
 * by the kind of change
 *)
val is_app : options -> goal_proof_diff -> bool

(* Get the kind of change *)
val get_change : options -> kind_of_change

(* Determine whether we are in the inductive case of search *)
val is_ind : options -> bool

(*
 * Udate the goals and terms for a diff.
 * Use the options to determine how to update the goals,
 * and replace the terms with the supplied old and new types.
 *)
val update_terms_goals :
  options -> types -> types -> goal_proof_diff -> goal_proof_diff

(*
 * Convert a search function that takes a set of options to a
 * search_function that is independent of options, which
 * can be used by zooming.
 *)
val to_search_function :
  (options -> goal_proof_diff -> candidates) -> options -> goal_proof_diff ->
  search_function
