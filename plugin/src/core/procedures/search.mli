(* Search procedures *)

open Constr
open Proofdiff
open Searchopts
open Evd
open Stateutils
open Environ

(*
 * Search for a patch given a difference in proofs
 * Return the default patch if we cannot find a patch
 * Otherwise, return any patch we can find
 *)
val search_for_patch :
  options ->
  env ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  constr state

