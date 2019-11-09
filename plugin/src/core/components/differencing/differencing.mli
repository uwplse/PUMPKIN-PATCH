(* --- Differencing Component --- *)

open Searchopts
open Differencers
open Evd
open Assumptions
open Environ
open Constr
open Stateutils
open Candidates

(*
 * Given a configuration, return the appropriate top-level differencer
 *)
val get_differencer :
  (equal_assumptions ->
   (env * env) ->
   (constr * constr) ->
   (types * types) ->
   evar_map ->
   candidates state) configurable
