open Searchopts
open Proofdiff
open Candidates
open Differencers
open Evd
open Stateutils
open Assumptions
open Environ
open Constr

(* --- Recursive differencing --- *)

(*
 * Try to difference with one differencer
 * If that fails, then try the next one, and so on
 *)
val try_chain_diffs :
  (equal_assumptions ->
   (env * env) ->
   (constr * constr) ->
   (types * types) ->
   evar_map ->
   candidates state) list ->
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state

(*
 * If p holds, apply diff_t
 * Otherwise, apply diff_f
 *
 * TODO before merging, move these type sigs back in somewhere
 *)
val branch_diff :
  (equal_assumptions ->
   (env * env) ->
   (constr * constr) ->
   (types * types) ->
   evar_map ->
   bool state) ->
  (equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state) ->
  (equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state) ->
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state
    
(*
 * Reduce and then diff
 * If reducing has no effect, then give up to prevent inifinite recursion
 *)
val diff_reduced :
  (equal_assumptions ->
   (env * env) ->
   (constr * constr) ->
   (types * types) ->
   evar_map ->
   candidates state) ->
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state

(*
 * Convert a proof differencer to a term differencer
 *
 * In other words, update the goals and terms of the current diff using
 * the supplied options, then apply the supplied differencing function
 * to the difference in terms.
 *)
val diff_terms :
  proof_differencer ->
  (equal_assumptions ->
   (env * env) ->
   (constr * constr) ->
   (types * types) ->
   (env * env) ->
   (constr * constr) ->
   evar_map ->
   candidates state) configurable

(*
 * Using some term differencer, recursively difference an array
 *)
val diff_map : term_differencer -> arr_list_differencer

(*
 * Using some term differencer, recursively difference an array
 * Flatten the resulting list
 *)
val diff_map_flat : term_differencer -> arr_differencer

(*
 * Apply some differencing function
 * Filter the result using the supplied modifier
 *)
val filter_diff :
  ('b -> evar_map -> 'b state) ->
  ('a, 'b) differencer ->
  ('a, 'b) differencer
