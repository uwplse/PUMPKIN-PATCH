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
  proof_differencer list ->
  proof_differencer

(*
 * If p holds, apply diff_t
 * Otherwise, apply diff_f
 *)
val branch_diff :
  proof_diff_predicate ->
  proof_differencer ->
  proof_differencer ->
  proof_differencer
    
(*
 * Reduce and then diff
 * If reducing has no effect, then give up to prevent inifinite recursion
 *)
val diff_reduced :
  proof_differencer ->
  proof_differencer

(*
 * Using some term differencer, recursively difference a list of differencers
 * in terms, with the environment and goals predetermined.
 *
 * TODO move to use term_differencer and arr_list_differencer again
 * once we finish porting these
 *)
val diff_map :
  (equal_assumptions ->
   (constr * constr) ->
   evar_map ->
   candidates state) ->
  args_differencer

(*
 * Like diff_map, but flatten the result
 *
 * TODO same as above
 *)
val diff_map_flat :
  (equal_assumptions ->
   (constr * constr) ->
   evar_map ->
   candidates state) ->
  args_differencer_flat

(*
 * Apply some differencing function
 * Filter the result using the supplied modifier
 *)
val filter_diff :
  ('b -> evar_map -> 'b state) ->
  ('a, 'b) differencer ->
  ('a, 'b) differencer
