(* --- Cutting by intermediate lemmas/guiding search --- *)

open Constr
open Environ
open Evd
open Stateutils

(*
 * Cut lemmas are guidance that the user can provide to help guide search
 * and circumvent shortcomings in the implementation of differencing.
 *
 * The hope is that these will eventually go away, but for now
 * they are useful.
 *)

type cut_lemma

(*
 * Build a cut lemma from an applied term
 *)
val build_cut_lemma : env -> types -> cut_lemma

(*
 * Get the type of the lemma to cut search by
 *)
val get_lemma : cut_lemma -> types

(*
 * Get the application of the lemma to cut by
 *)
val get_app : cut_lemma -> types

(*
 * Test if a term has exactly the type of the lemma to cut by
 * This term cannot have extra hypotheses
 *)
val has_cut_type_strict :
  env -> cut_lemma -> types -> evar_map -> bool state

(*
 * Test if a term has exactly the type of the lemma to cut by in reverse
 * This term cannot have extra hypotheses
 *)
val has_cut_type_strict_rev :
  env -> cut_lemma -> types -> evar_map -> bool state

(*
 * Test if a term has the type of the lemma or its reverse
 *)
val has_cut_type_strict_sym :
  env -> cut_lemma -> types -> evar_map -> bool state

(*
 * Filter a list of terms to those that have the cut lemma type
 * These terms can have extra hypotheses
 *)
val filter_cut :
  env -> cut_lemma -> types list -> evar_map -> (types list) state

(*
 * Filter a list of terms to those that apply the cut lemma type
 * These terms can have extra hypotheses
 *)
val filter_applies_cut :
  env -> cut_lemma -> types list -> evar_map -> (types list) state

(*
 * Filter a list of terms to those that are consistent with the cut type
 * Offset these terms by the same amount (so return the subterm
 * that actually can have the cut type).
 *)
val filter_consistent_cut :
  env -> cut_lemma -> types list -> types list

(*
 * This returns true when the candidates we have patch the lemma we cut by
 *)
val are_cut :
  env -> cut_lemma -> types list -> evar_map -> bool state
