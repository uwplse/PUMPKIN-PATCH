(* Search configuration *)

open Term
open Environ
open Proofdiff
open Cutlemma
open Kindofchange

(* --- Options for search --- *)

type options

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

(* Set the kind of change *)
val set_change : options -> kind_of_change -> options

(* Determine whether we are in the inductive case of search *)
val is_ind : options -> bool

(* Set the inductive case flag *)
val set_is_ind : options -> bool -> options

(* --- Type difference detection & search configuration --- *)

(* Build configuration options for the search *)
val configure_search :
  goal_proof_diff -> kind_of_change -> cut_lemma option -> options
