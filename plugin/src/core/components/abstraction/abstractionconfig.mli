open Environ
open Term
open Abstracters
open Candidates

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

(* Configure abstraction for a fixpoint *)
val configure_fixpoint_cases :
  env -> types list -> candidates -> abstraction_config list
