open Environ
open Term
open Abstracters
open Candidates
open Searchopts
open Proofdiff

(* --- Configuring Abstraction --- *)

(* Caller configuration for abstraction *)
type abstraction_config =
  {
    env : env;
    args_base : types list;
    args_goal : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : abstraction_strategy list;
  }

(* --- Defaults --- *)

(*
 * Given an environment, a difference in goal types, and a list of candidates,
 * configure the default configuration for abstraction of arguments
 *)
val configure_args :
  env -> types proof_diff -> candidates -> abstraction_config

(*
 * Given an environment, a list of differences between fixpoint cases,
 * and a list of candidates, configure function abstraction.
 *
 * This produces one configuration for each difference.
 *)
val configure_fixpoint_cases :
  env -> types list -> candidates -> abstraction_config list

(* --- Cut Lemmas --- *)

(*
 * These configuration functions are for when you cut search by a certain lemma,
 * so the type of the candidate may not be formatted well enough to infer how
 * to abstract it, but the supplied cut lemma type may be.
 * In those cases, we go with the cut lemma, though improvements
 * to search and abstraction should make this obsolete.
 *)

(*
 * Given an environment, a lemma to cut by, and a list of candidates,
 * configure argument abstraction.
 *)
val configure_cut_args :
  env -> cut_lemma -> candidates -> abstraction_config

(* --- Goals --- *)

(*
 * These configuration functions are for the top-level abstract
 * command, which takes a goal type. We use the goal type
 * to infer how to abstract the function rather than the type of the candidate,
 * since this gives the user more control over abstraction.
 *)

(*
 * Give an environment, a goal type, and a candidate, configure function
 * abstraction.
 *)
val configure_fun_from_goal :
  env -> types -> types -> abstraction_config
