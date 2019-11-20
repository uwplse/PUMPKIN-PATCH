(* Expanding proof categories *)

open Environ
open Constr
open Proofcat
open Evd
open Stateutils

(* --- Type definitions --- *)

type 'a expansion_strategy = 'a -> evar_map -> 'a state

(* --- Categories --- *)

(*
 * Expand the terminal object of a proof category exactly once
 * Return the original category if it cannot be exapnded
 *)
val expand_terminal : proof_cat expansion_strategy

(*
 * Expand an inductive constructor
 * That is, expand its conclusion fully if it is dependent
 * Then mark the edges that are inductive hypotheses
 *)
val expand_constr : proof_cat expansion_strategy

(*
 * Expand an application arrow
 *
 * This assumes it's the only arrow in c
 * Otherwise, there is an error
 * Like the above, this will not work yet when induction is later in the proof
 *)
val eval_induction_cat :
  Assumptions.equal_assumptions -> env * env -> constr * constr -> evar_map -> (proof_cat * proof_cat * Assumptions.equal_assumptions) state
