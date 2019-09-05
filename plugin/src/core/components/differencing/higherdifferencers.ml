open Constr
open Proofdiff
open Utilities
open Candidates
open Reducers
open Differencers
open Searchopts

(* --- Recursive differencing --- *)

(*
 * Try to difference with one differencer
 * If that fails, then try the next one
 *)
let rec try_chain_diffs diffs d evd =
  match diffs with
  | diff_h :: diff_t ->
     let cs = snd (diff_h d evd) in
     if non_empty cs then
       cs
     else
       try_chain_diffs diff_t d evd
  | _ ->
     give_up

(*
 * Try to reduce and then diff
 * If reducing does not change the term, then give_up to prevent
 * inifinite recursion
 *)
let diff_reduced diff d sigma =
  let (o, n) = proof_terms d in
  let d_red = snd (reduce_diff reduce_term d Evd.empty) in
  let (o_red, n_red) = proof_terms d_red in
  if not ((equal o o_red) && (equal n n_red)) then
    diff d_red sigma
  else
    sigma, give_up

(*
 * Convert a differencing function that takes a diff into one between two terms
 *
 * In other words, take an old diff d with assumptions that still hold, and:
 * 1. Update the terms and goals of the diff d to use those terms
 * 2. Apply the differencing function to the new diff
 *)
let diff_terms (diff : proof_differencer) d opts d_t sigma =
  diff (snd (update_terms_goals opts (old_proof d_t) (new_proof d_t) d Evd.empty)) sigma

(*
 * Recursively difference each term in a diff of arrays
 *)
let diff_map (diff : term_differencer) d_arr sigma =
  let assums = assumptions d_arr in
  List.map2
    (fun t_o t_n -> snd (diff (difference t_o t_n assums) sigma))
    (Array.to_list (old_proof d_arr))
    (Array.to_list (new_proof d_arr))

(*
 * Recursively difference each term in a diff of arrays
 * Flatten the result
 *)
let diff_map_flat (diff : term_differencer) d_arr sigma =
  Evd.empty, List.flatten (diff_map diff d_arr sigma)

(*
 * Apply some differencing function
 * Filter the result using the supplied modifier
 *)
let filter_diff filter (diff : ('a, 'b) differencer) d : 'b =
  filter (diff d)
