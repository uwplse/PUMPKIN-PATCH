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
open Evd
open Stateutils
open Proofcat
open Proofcatterms
open Evaluation
open Kindofchange
open Inference

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
             (diff_fix_cases env (old_type, new_type, no_assumptions))
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
 *
 * TODO finish decatifying & clean before merging
 *)
let search_for_patch opts env terms goals sigma =
  Printf.printf "%s\n\n" "----";
  let default = snd terms in
  let change = get_change opts in
  let start_backwards = is_fixpoint_case change || is_hypothesis change in
  let assums = no_assumptions in
  let envs = env, env in
  let terms = if start_backwards then (snd terms, fst terms) else terms in
  let sigma, typ_o = infer_type env sigma (fst terms) in
  let sigma, typ_n = infer_type env sigma (snd terms) in
  let goals = (typ_o, typ_n) in
  let sigma, d = update_search_goals opts assums envs terms goals envs terms sigma in
  let diff = get_differencer opts in
  let sigma_non_rev, patches = diff d sigma in
  let (goal_o, o), (goal_n, n), assums = d in
  let _, env = dest_context_term goal_o in
  if non_empty patches then
    return_patch opts env patches sigma_non_rev
  else
    let d_rev = (goal_n, n), (goal_o, o), reverse_assumptions assums in
    let sigma_rev, rev_patches = diff d_rev sigma in
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
