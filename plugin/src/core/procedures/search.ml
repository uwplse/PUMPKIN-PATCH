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

(* --- General proof terms --- *)

(*
 * Search for a direct patch given a difference in proof_cats within.
 * This is a collection of heuristics, which
 * we have numbered for clarity, and which we explain at the bottom
 * where it's closest to the code. Unimplemented heuristics
 * give_up (return the empty list).
 *
 * There is more work to make this generalize. For example, to handle
 * two proofs (f x) and (g y), where we can find (f -> g) and (y -> x),
 * we need to apply search_app as well. However, we don't always want to do
 * this, and doing this breaks some of our benchmark proofs. So when
 * we implement that benchmark, we need to consider how to determine
 * when to recurse that way. It's only immediately clear right now
 * for the inductive case in (3). Another missing example is
 * unwrapping function definitions. More missing features are in Trello.
 *
 * Heuristics, explained:
 * 1. When the proofs are definitionally equal, return the identity patch
 * 2a. When the proofs induct over the same hypotheses, then search
 *    the inductive proof for a patch, then get the leftover arguments.
 *    Apply a recursive patch for the first leftover argument,
 *    since it is the argument that induction occurred over.
 *    Ignore other hypotheses since our patch in the inductive case is direct.
 *    The "same hypothesis" depends on the kind of search: If it's a search
 *    for a difference in conclusions, then they must be exactly the same,
 *    but if it's for a difference in types, then they must be the same
 *    modulo those types (for now, they must be exactly those types).
 *    This heuristic is incomplete in its reasoning about leftover arguments.
 * 2b. When the condition for 2a holds but 2a fails, then treat it like 6a.
 * 3. When the proofs are inductive cases of a larger inductive proof,
 *    and we encounter a function that applies the inductive hypothesis,
 *    eliminate the IHs from the arguments and search
 *    for a patch recursively from function to function (forwards)
 *    and arguments to arguments (backwards).
 * 4. When both terms are lambdas, and there's a common argument
 *    type to both lambdas, then assume they are equal and zoom in.
 *    Look for a patch going from the common argument to the zoomed in
 *    term.
 * 5. When both terms are lambdas, there isn't a common argument,
 *    and we're either in the inductive case or dealing with a change,
 *    in types, then zoom in and search there like we would for common
 *    argument, but don't wrap it in a lambda (throw out the last argument).
 * 6a. When one proof term may apply the other and
 *    none of the other heuristics fire, then we use find_difference
 *    to try to find a direct patch by looking at the terms themselves.
 * 6b. When the condition for 6a holds but 6a fails, then treat it like 3.
 *)
let rec search (opts : options) (d : goal_proof_diff) : candidates =
  let d = reduce_letin (reduce_casts d) in
  let search_ind = fun opts -> diff_inductive opts search in
  if no_diff opts d then
    (*1*) identity_candidates d
  else if induct_over_same_h (same_h opts) d then
    (*2a*) let patches = diff_app_ind opts search_ind search d in
    if non_empty patches then
      patches
    else
      (*2b*) find_difference opts d
  else if applies_ih opts d then
    (*3*) diff_app opts search search (reduce_trim_ihs d)
  else
    match kinds_of_terms (proof_terms d) with
    | (Lambda (n_o, t_o, b_o), Lambda (_, t_n, b_n)) ->
       if no_diff opts (eval_with_terms t_o t_n d) then
         (*4*) zoom_wrap_lambda (to_search_function search opts d) n_o t_o d
       else
         if is_ind opts || not (is_conclusion (get_change opts)) then
           (*5*) zoom_unshift (to_search_function search opts d) d
         else
           give_up
    | _ ->
       if is_app opts d then
         (*6a*) let patches = find_difference opts d in
         if non_empty patches then
           patches
         else
           (*6b*) let patches = diff_app opts search search d in
           if non_empty patches then
             patches
           else
             (* 6c TODO explain, refactor, support better *)
             let (o, n) = proof_terms d in
             let d_red = reduce_diff reduce_term d in
             let (o_red, n_red) = proof_terms d_red in
             if not ((eq_constr o o_red) && (eq_constr n n_red)) then
               search opts d_red
             else
               give_up
       else
         give_up

(* Given a configuration, return the appropriate search function *)
let search_function (opts : options) (should_reduce : bool) =
  if should_reduce then
    (fun opts d -> search opts (reduce_diff reduce_term d))
  else
    search

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
  let should_reduce = is_inductive_type change in
  let search = search_function opts should_reduce in
  let patches = search opts d in
  let ((_, env), _) = old_proof (dest_goals d) in
  if non_empty patches then
    return_patch opts env patches
  else
    let rev_patches = search opts (reverse d) in
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
