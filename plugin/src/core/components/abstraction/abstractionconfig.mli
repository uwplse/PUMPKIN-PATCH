open Environ
open Term
open Abstracters
open Candidates
open Searchopts

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

(*
 * Given an environment, a list of differences between fixpoint cases,
 * and a list of candidates, configure function abstraction.
 *
 * This produces one configuration for each difference.
 *)
val configure_fixpoint_cases :
  env -> types list -> candidates -> abstraction_config list

(*
 * Given an environment, a lemma to cut by, and a list of candidates,
 * configure argument abstraction.
 *)
val configure_cut_args :
  env -> cut_lemma -> candidates -> abstraction_config
