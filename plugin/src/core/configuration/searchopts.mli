(* Search configuration *)

open Term
open Environ
open Proofdiff

(* --- Cutting by intermediate lemmas/guiding search --- *)

(*
 * Most of this should go away eventually, but we need it until we improve
 * type difference detection
 *)

type cut_lemma

(* Build a cut lemma from an applied term *)
val build_cut_lemma : env -> types -> cut_lemma

(* Get the type of the lemma to cut search by *)
val get_lemma : cut_lemma -> types

(* Get the application of the lemma to cut by *)
val get_app : cut_lemma -> types

(*
 * Test if a term has exactly the type of the lemma to cut by
 * This term cannot have extra hypotheses
 *)
val has_cut_type_strict : env -> cut_lemma -> types -> bool

(*
 * Test if a term has exactly the type of the lemma to cut by in reverse
 * This term cannot have extra hypotheses
 *
 * POST-DEADLINE: Having both of these is messy/creates extra candidates.
 * Determine which one to use based on search goals, direction, options,
 * and candidates.
 *)
val has_cut_type_strict_rev : env -> cut_lemma -> types -> bool

(* Test if a term has the type of the lemma or its reverse *)
val has_cut_type_strict_sym : env -> cut_lemma -> types -> bool

(*
 * Filter a list of terms to those that have the cut lemma type
 * These terms can have extra hypotheses
 *)
val filter_cut : env -> cut_lemma -> types list -> types list

(*
 * Filter a list of terms to those that apply the cut lemma type
 * These terms can have extra hypotheses
 *)
val filter_applies_cut : env -> cut_lemma -> types list -> types list

(*
 * This returns true when the candidates we have patch the lemma we cut by
 *)
val are_cut : env -> cut_lemma -> types list -> bool

(* --- Kinds of changes --- *)

(*
 * Represents the kind of change we are searching for, for now either:
 * 1) A change in conclusions, or
 * 2) A change in an inductive type we are doing induction over that preserves
 *    the shape of the inductive type
 * 3) A change in a fixpoint
 *    definition we are proving a property about inductively
 *    that preserves the shape of the definition
 * 4) A change in conclusions of a case of an inductive type that definitely
 *    cannot be factored out (or that the user does not want to factor out),
 *    as in proofs of properties via constructors like exists
 *)
type kind_of_change =
  | Conclusion
  | InductiveType of types * types
  | FixpointCase of (types * types) * cut_lemma
  | ConclusionCase of (cut_lemma option)

val is_conclusion : kind_of_change -> bool
val is_inductive_type : kind_of_change -> bool
val is_fixpoint_case : kind_of_change -> bool
val is_conclusion_case : kind_of_change -> bool

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
val configure_search : goal_proof_diff -> cut_lemma option -> options
