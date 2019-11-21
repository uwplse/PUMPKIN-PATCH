(* Expanding proof categories *)
(* TODO delete me *)

open Environ
open Constr
open Proofcat
open Evd
open Stateutils

(* --- Type definitions --- *)

type 'a expansion_strategy = 'a -> evar_map -> 'a state

