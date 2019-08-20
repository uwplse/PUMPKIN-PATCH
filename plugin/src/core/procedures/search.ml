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
let return_patch opts env evd (patches : types list) : types =
  match get_change opts with
  | FixpointCase ((old_type, new_type), cut) ->
     let body_reducer = specialize_in (get_app cut) specialize_term in
     let reduction_condition en evd tr = has_cut_type_strict_sym en cut tr evd in
     let reducer = reduce_body_if reduction_condition body_reducer in
     let _, specialized = reduce_all reducer env evd patches in
     let specialized_fs = List.map (factor_term env evd) specialized in
     let specialized_fs_terms = flat_map reconstruct_factors specialized_fs in
     let generalized =
       flat_map
         abstract_with_strategies
         (configure_fixpoint_cases
            env
            evd
            (diff_fix_cases env evd (difference old_type new_type no_assumptions))
            specialized_fs_terms)
     in List.hd generalized (* TODO better failure when none found *)
  | ConclusionCase (Some cut) ->
     let _, patches = reduce_all remove_unused_hypos env evd patches in
     let generalized =
       abstract_with_strategies
         (configure_cut_args env evd cut patches)
     in List.hd generalized (* TODO better failure when none found *)
  | Hypothesis (_, _) ->
     let _, patches = reduce_all remove_unused_hypos env evd patches in
     List.hd patches
  | _ ->
     Printf.printf "%s\n" "SUCCESS";
     List.hd patches

(*
 * The top-level search procedure!
 *
 * Search in one direction, and if we fail try the other direction.
 * If we find patches, return the head for now, since any patch will do.
 *)
let search_for_patch evd (default : types) (opts : options) (d : goal_proof_diff) : types =
  Printf.printf "%s\n\n" "----";
  let change = get_change opts in
  let start_backwards = is_fixpoint_case change || is_hypothesis change in
  let d = if start_backwards then reverse d else d in (* explain *)
  let d = update_search_goals opts d (erase_goals d) in
  let diff = get_differencer opts evd in
  let patches = diff d in
  let ((_, env), _) = old_proof (dest_goals d) in
  if non_empty patches then
    return_patch opts env evd patches
  else
    let rev_patches = diff (reverse d) in
    Printf.printf "%s\n" "searched backwards";
    Printf.printf "inverting %d candidates\n" (List.length rev_patches);
    let inverted = invert_terms invert_factor env evd rev_patches in
    if non_empty inverted then
      return_patch opts env evd inverted
    else
      match change with
      | Conclusion | (Hypothesis (_, _)) ->
         let patch = default in
         Printf.printf "%s\n" "FAILURE";
         patch
      | _ ->
         failwith "Could not find patch"
