(* Search procedures *)

open Utilities
open Environ
open Constr
open Assumptions
open Abstraction
open Abstractionconfig
open Proofdiff
open Reducers
open Specialization
open Inverting
open Searchopts
open Factoring
open Fixdifferencers
open Differencing
open Cutlemma
open Kindofchange
open Evd
open Stateutils

(* --- Procedure --- *)

(*
 * Determines final processing step for a patch candidate based on the
 * procedure/options.
 *
 * Mostly this is which components to call in the last
 * iteration of the "while not expanded" loop,
 * but it's messy because I had to workaround DeBruijn
 * inconsistencies and deal with user-cut lemmas
 * in the prototype. I'll fix this one day.
 *
 * The biggest limitation is that in some cases, we use a function
 * that removes unused hypotheses rather than ensuring we get exactly
 * the type we initially asked for. We can always reconstruct such a function
 * into something with that type, but that isn't yet implemented. This is to
 * get around annoying unused hypotheses that are useful to assume during the
 * search process, but it's accidentally eliminating unused hypotheses
 * that are also in the goal. Again, because we get something strictly strongly,
 * not a huge deal, but this gives us a weaker idea of when to apply these
 * patches, which will matter eventually.
 *)
let return_patch opts env (patches : types list) =
  let ret_patch cs = ret (List.hd cs) (* TODO better failure when empty *) in
  let reduce_patches reducer sigma = reduce_all reducer env sigma patches in
  match get_change opts with
  | FixpointCase ((old_type, new_type), cut) ->
     let body_reducer = specialize_in (get_app cut) specialize_term in
     let do_reduce env sigma tr = has_cut_type_strict_sym env cut tr sigma in
     let reducer = reduce_body_if do_reduce body_reducer in
     bind
       (bind
          (bind (reduce_patches reducer) (map_state (factor_term env)))
          (fun fs -> ret (flat_map reconstruct_factors fs)))
       (fun fs ->
         bind
           (bind
             (diff_fix_cases env (difference old_type new_type no_assumptions))
             (fun cs ->
               bind
                 (configure_fixpoint_cases env cs fs)
                 (flat_map_state abstract_with_strategies)))
           ret_patch)
  | ConclusionCase (Some cut) ->
     bind
       (bind
          (bind
             (reduce_patches remove_unused_hypos)
             (configure_cut_args env cut))
          abstract_with_strategies)
       ret_patch
  | Hypothesis (_, _) ->
     bind (reduce_patches remove_unused_hypos) ret_patch
  | _ ->
     Printf.printf "%s\n" "SUCCESS";
     ret_patch patches

(*
 * The top-level search procedure!
 *
 * Search in one direction, and if we fail try the other direction.
 * If we find patches, return the head for now, since any patch will do.
 *)
let search_for_patch (default : types) (opts : options) (d : goal_proof_diff) sigma =
  Printf.printf "%s\n\n" "----";
  let change = get_change opts in
  let start_backwards = is_fixpoint_case change || is_hypothesis change in
  let d = if start_backwards then reverse d else d in (* explain *)
  let sigma, d = update_search_goals opts d (erase_goals d) sigma in
  let diff = get_differencer opts in
  let sigma_non_rev, patches = diff d sigma in
  let ((_, env), _) = old_proof (dest_goals d) in
  if non_empty patches then
    return_patch opts env patches sigma_non_rev
  else
    let sigma_rev, rev_patches = diff (reverse d) sigma in
    Printf.printf "%s\n" "searched backwards";
    Printf.printf "inverting %d candidates\n" (List.length rev_patches);
    let sigma_inv, inverted = invert_terms invert_factor env rev_patches sigma_rev in
    if non_empty inverted then
      return_patch opts env inverted sigma_inv
    else
      match change with
      | Conclusion | (Hypothesis (_, _)) ->
         let patch = default in
         Printf.printf "%s\n" "FAILURE";
         sigma, patch
      | _ ->
         failwith "Could not find patch"
