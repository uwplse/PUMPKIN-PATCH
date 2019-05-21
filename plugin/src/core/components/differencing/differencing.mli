(* --- Differencing Component --- *)

open Searchopts
open Differencers
open Evd

(*
 * Given a configuration, return the appropriate top-level differencer
 *)
val get_differencer : (evar_map -> proof_differencer) configurable
