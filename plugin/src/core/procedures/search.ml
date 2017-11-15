(* Search procedures *)

open Environ
open Term
open Coqterms
open Coqenvs
open Debruijn
open Proofcat
open Proofcatterms
open Assumptions
open Abstracters
open Abstraction
open Abstractionconfig
open Filters
open Proofdiff
open Reducers
open Specialization
open Evaluation
open Expansion
open Printing
open Collections
open Utilities
open Hofs
open Inverting
open Searchopts
open Factoring
open Differencing
open Candidates
open Zooming
open Cutlemma
open Kindofchange

(* --- Debugging --- *)

(* Debug the search function *)
let debug_search (d : goal_proof_diff) : unit =
  let (t_o, t_n) = proof_terms d in
  let d = dest_goals d in
  let ((old_goal, env_o), _) = old_proof d in
  let ((new_goal, env_n), _) = new_proof d in
  debug_term env_o t_o "old";
  debug_term env_n t_n "new";
  debug_term env_o old_goal "old goal";
  debug_term env_n new_goal "new goal";
  print_separator ()

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
 *)
let return_patch (opts : options) (env : env) (patches : types list) : types =
  match get_change opts with
  | FixpointCase ((old_type, new_type), cut) ->
     let body_reducer = specialize_in (get_app cut) specialize_term in
     let reduction_condition en tr = has_cut_type_strict_sym en cut tr in
     let reducer = reduce_body_if reduction_condition body_reducer in
     let specialized = List.map (reducer env) patches in
     let specialized_fs = List.map (factor_term env) specialized in
     let specialized_fs_terms = flat_map reconstruct_factors specialized_fs in
     let generalized =
       flat_map
         abstract_with_strategies
         (configure_fixpoint_cases
            env
            (diff_fix_cases env (difference old_type new_type no_assumptions))
            specialized_fs_terms)
     in List.hd generalized
  | ConclusionCase (Some cut) ->
     let patches = reduce_all remove_unused_hypos env patches in
     let generalized =
       abstract_with_strategies
         (configure_cut_args env cut patches)
     in List.hd generalized
  | _ ->
     Printf.printf "%s\n" "SUCCESS";
     List.hd patches

(*
 * The top-level search function!
 *
 * Search in one direction, and if we fail try the other direction.
 * If we find patches, return the head for now, since any patch will do.
 *)
let search_for_patch (default : types) (opts : options) (d : goal_proof_diff) : types =
  Printf.printf "%s\n\n" "----";
  let change = get_change opts in
  let d = if is_fixpoint_case change then reverse d else d in  (* explain *)
  let d = update_search_goals opts d (erase_goals d) in
  let diff = get_differencer opts in
  let patches = diff d in
  let ((_, env), _) = old_proof (dest_goals d) in
  if non_empty patches then
    return_patch opts env patches
  else
    let rev_patches = diff (reverse d) in
    Printf.printf "%s\n" "searched backwards";
    Printf.printf "inverting %d candidates\n" (List.length rev_patches);
    let inverted = invert_terms invert_factor env rev_patches in
    match change with
    | Conclusion ->
       if non_empty inverted then
         let patch = List.hd inverted in
         Printf.printf "%s\n" "SUCCESS";
         patch
       else
         let patch = default in
         Printf.printf "%s\n" "FAILURE";
         patch
    | _ ->
       if non_empty inverted then
         return_patch opts env inverted
       else
         failwith "Could not find patch"
