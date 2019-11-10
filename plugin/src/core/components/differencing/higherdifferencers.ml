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
let rec try_chain_diffs diffs assums envs terms goals =
  match diffs with
  | diff_h :: diff_t ->
     bind
       (diff_h assums envs terms goals)
       (fun cs ->
         if non_empty cs then
           ret cs
         else
           try_chain_diffs diff_t assums envs terms goals)
  | _ ->
     ret give_up

(*
 * If p holds, apply diff_t
 * Otherwise, apply diff_f
 *)
let branch_diff p diff_t diff_f assums envs terms goals =
  branch_state
    (fun _ -> p assums envs terms goals)
    (fun _ -> diff_t assums envs terms goals)
    (fun _ -> diff_f assums envs terms goals)
    ()
  
(*
 * Try to reduce and then diff
 * If reducing does not change the term, then give_up to prevent
 * inifinite recursion
 *)
let diff_reduced diff assums envs terms goals sigma =
  let sigma, term_o = reduce_term (fst envs) sigma (fst terms) in
  let sigma, term_n = reduce_term (snd envs) sigma (snd terms) in
  if not ((equal (fst terms) term_o) && (equal (snd terms) term_n)) then
    diff assums envs (term_o, term_n) goals sigma
  else
    ret give_up sigma

(*
 * Convert a differencing function that takes a diff into one between two terms
 *
 * In other words, take an old diff d with assumptions that still hold, and:
 * 1. Update the terms and goals of the diff d to use those terms
 * 2. Apply the differencing function to the new diff
 *)
let diff_terms (diff : proof_differencer) opts assums envs terms goals envs_next terms_next =
  bind
    (update_search_goals opts envs terms goals envs_next terms_next)
    (fun (envs, terms, goals) sigma ->
      let sigma, o = Evaluation.eval_proof (fst envs) (fst terms) sigma in
      let sigma, n = Evaluation.eval_proof (snd envs) (snd terms) sigma in
      let goal_o = Proofcat.Context (Proofcat.Term (fst goals, fst envs), fid ()) in
      let goal_n = Proofcat.Context (Proofcat.Term (snd goals, snd envs), fid ()) in
      let d = ((goal_o, o), (goal_n, n), assums) in
      diff d sigma)

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
