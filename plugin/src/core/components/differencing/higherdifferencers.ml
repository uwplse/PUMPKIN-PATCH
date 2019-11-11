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
 * Using some term differencer, recursively difference a list of differencers
 * in terms, with the environment and goals predetermined
 *)
let diff_map diff assums (os, ns) =
  map2_state (fun t_o t_n -> diff assums (t_o, t_n)) os ns

(*
 * Like diff_map, but flatten the result
 *)
let diff_map_flat diff assums (os, ns) =
  bind (diff_map diff assums (os, ns)) (fun l -> ret (List.flatten l))

(*
 * Apply some differencing function
 * Filter the result using the supplied modifier
 *)
let filter_diff filter (diff : ('a, 'b) differencer) d =
  bind (diff d) filter
