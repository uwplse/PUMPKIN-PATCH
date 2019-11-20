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
 * Expand an inductive constructor
 * That is, expand its conclusion fully if it is dependent
 * Then mark the edges that are inductive hypotheses
 *)
val expand_constr : proof_cat expansion_strategy
