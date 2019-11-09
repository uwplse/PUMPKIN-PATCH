open Constr
open Proofdiff
open Utilities
open Candidates
open Reducers
open Differencers
open Searchopts
open Stateutils

(* --- Recursive differencing --- *)

(*
 * Try to difference with one differencer
 * If that fails, then try the next one
 *)
let rec try_chain_diffs diffs d =
  match diffs with
  | diff_h :: diff_t ->
     bind
       (diff_h d)
       (fun cs ->
         if non_empty cs then
           ret cs
         else
           try_chain_diffs diff_t d)
  | _ ->
     ret give_up

(*
 * Try to reduce and then diff
 * If reducing does not change the term, then give_up to prevent
 * inifinite recursion
 *)
let diff_reduced diff d =
  let (o, n) = proof_terms d in
  bind
    (reduce_diff reduce_term d)
    (fun d_red ->
      let (o_red, n_red) = proof_terms d_red in
      if not ((equal o o_red) && (equal n n_red)) then
        diff d_red
      else
        ret give_up)

(*
 * Convert a differencing function that takes a diff into one between two terms
 *
 * In other words, take an old diff d with assumptions that still hold, and:
 * 1. Update the terms and goals of the diff d to use those terms
 * 2. Apply the differencing function to the new diff
 *)
let diff_terms (diff : proof_differencer) opts assums envs terms goals envs_next terms_next =
  bind (update_search_goals opts assums envs terms goals envs_next terms_next) diff

(*
 * Recursively difference each term in a diff of arrays
 *)
let diff_map (diff : term_differencer) (os, ns, assums) =
  let (os, ns) = map_tuple Array.to_list (os, ns) in
  map2_state (fun t_o t_n -> diff (t_o, t_n, assums)) os ns

(*
 * Recursively difference each term in a diff of arrays
 * Flatten the result
 *)
let diff_map_flat (diff : term_differencer) d_arr =
  bind (diff_map diff d_arr) (fun l -> ret (List.flatten l))

(*
 * Apply some differencing function
 * Filter the result using the supplied modifier
 *)
let filter_diff filter (diff : ('a, 'b) differencer) d =
  bind (diff d) filter
