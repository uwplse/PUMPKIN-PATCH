(* Expanding proof categories *)
(* TODO delete me *)

open Stateutils
open Names
open Environ
open Evd
open Constr
open Proofcat
open Proofcatterms
open Evaluation
open Utilities
open Debruijn
open Declarations
open Indutils
open Contextutils
open Convertibility
open Envutils
open Inference
open Checking
open Evaluation

(* --- Type definitions --- *)

type 'a expansion_strategy = 'a -> evar_map -> 'a state



