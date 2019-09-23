(* --- Differencing of Proofs --- *)

open Evd
open Searchopts
open Differencers
open Assumptions
open Proofcat
open Searchopts
open Stateutils
open Constr
open Environ

(*
 * TODO move this type signature back to proofdiff in the end before merging
 *)

(*
 * Primitive differencing function
 *)
val find_difference :
  options ->
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  constr list state

(*
 * Determine if two proof diffs are identical
 *)
val no_diff :
  options ->
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  bool state

(*
 * Return the identity candidates applied to the type
 * of the new proof in the diff
 *)
val identity_candidates :
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  constr list state
