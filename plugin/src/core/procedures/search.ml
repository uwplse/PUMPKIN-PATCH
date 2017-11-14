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

(* --- Induction --- *)

(*
 * Given an ordered pair of lists of arrows to explore in a case of an
 * inductive proof, difference each one (using diff).
 * As soon as we find candidates that can be properly abstracted
 * (using abstract), return those. Otherwise, recurse.
 *
 * For now, we don't combine these in any way, and just look at the
 * difference between each pair, but without changing the goal type.
 * In the future we may want to be smarter about this.
 * To improve this, we need benchmarks for which the head is not the patch,
 * but another arrow is.
 *)
let rec diff_cases abstract diff (d : goal_case_diff) : candidates =
  let d_goal = erase_proofs d in
  match diff_proofs d with
  | ((h1 :: t1), (h2 :: t2)) ->
     let d_t = add_to_diff d_goal t1 t2 in
     (try
        let c1 = eval_proof_arrow h1 in
        let c2 = eval_proof_arrow h2 in
        let cs = abstract (diff (add_to_diff d_goal c1 c2)) in
        if non_empty cs then
          cs
        else
          diff_cases abstract diff d_t
      with _ ->
        diff_cases abstract diff d_t)
  | _ ->
     give_up

(*
 * Given an ordered pair of lists of arrows to explore in the base case,
 * search the difference between each one.
 *
 * Stop as soon as we find a patch and return any of the patches.
 *
 * We try to lift the candidates we find for changes in conclusions.
 * Right now we don't handle the constructor argument case because it should
 * never get here, but if proofs are nested they could,
 * so we need to extend this for that later.
 *
 * When it's a change in constructor or fixpoint case then
 * we don't lift, but we could eventually try to apply the induction
 * principle for the constructor version to get a more general patch.
 *)
let diff_case_paths opts diff (d : goal_case_diff) : candidates =
  let d_goal = erase_proofs d in
  let env = context_env (old_proof d_goal) in
  diff_cases
    (fun cs ->
      match get_change opts with
      | InductiveType (_, _) ->
         cs
      | FixpointCase ((_, _), cut) when are_cut env cut cs ->
         cs
      | _ ->
         try_abstract_inductive d_goal cs)
    (diff opts)
    d

(*
 * Update the assumptions in a case of the inductive proof
 * Shift by the number of morphisms in the case,
 * assuming they are equal when they are convertible
 *)
let update_case_assums (d : proof_cat_diff) ms_o ms_n : equal_assumptions =
  List.fold_left2
    (fun assums dst_o dst_n ->
      let d_dest = difference dst_o dst_n assums in
      let (env, d_goal, _) = merge_lift_diff_envs d_dest [] in
      if convertible env (old_proof d_goal) (new_proof d_goal) then
        assume_local_equal assums
      else
        shift_assumptions assums)
    (assumptions d)
    (conclusions (remove_last ms_o))
    (conclusions (remove_last ms_n))

(*
 * Search a case of a difference in proof categories.
 * Return a patch if we find one.
 *
 * This breaks it up into arrows and then searches those
 * in the order of the sort function.
 *)
let search_case search opts sort (d : proof_cat_diff) : candidates =
  let o = old_proof d in
  let n = new_proof d in
  let ms_o = morphisms o in
  let ms_n = morphisms n in
  diff_case_paths
    opts
    search
    (reset_case_goals
       opts
       (map_diffs
          (fun (o, ms) -> (terminal o, ms))
          (always (update_case_assums d ms_o ms_n))
          (add_to_diff d (sort o ms_o) (sort n ms_n))))

(*
 * Base case: Prefer arrows later in the proof
 *)
let search_base_case search opts (d : proof_cat_diff) : candidates =
  let sort _ ms = List.rev ms in
  search_case search (set_is_ind opts false) sort d

(*
 * Inductive case: Prefer arrows closest to an IH,
 * and in a tie, prefer arrows that are later.
 *
 * There currently may not be a guarantee that the two
 * arrows are traversed in exactly the same order for each proof.
 * If there is a bug in this, this may be why.
 *)
let search_inductive_case search opts (d : proof_cat_diff) : candidates =
  let sort c ms = List.stable_sort (closer_to_ih c (find_ihs c)) ms in
  search_case search (set_is_ind opts true) sort d

(*
 * Search in a case, then adjust the patch so it type-checks
 * in the original envionment.
 *
 * If there is a bug here, then the unshift number may not generalize
 * for all cases.
 *)
let search_and_check_case search opts (d : proof_cat_diff) : candidates =
  let o = expand_constr (old_proof d) in
  let n = expand_constr (new_proof d) in
  let assums = assumptions d in
  let d = difference o n assums in
  let offset =
    if is_conclusion (get_change opts) then
      List.length (morphisms o)
    else
      0
  in
  List.map
    (unshift_by offset)
    (if has_ihs o then
       search_inductive_case search opts d
     else
       search_base_case search opts d)

(*
 * Search in a diff that has been broken up into different cases.
 * That is, search the base case, inductive case, and so on separately.
 *
 * For now, we only return the first patch we find.
 * We may want to return more later.
 *)
let rec search_and_check_cases search opts (ds : proof_cat_diff list) : candidates =
  match ds with
  | d :: tl ->
     let patches = search_and_check_case search opts d in
     if non_empty patches then
       patches
     else
       search_and_check_cases search opts tl
  | [] ->
     []

(*
 * Sort cs so that the base cases are first in the list
 * This is not yet tested
 * This is also not yet optimized
 *)
let base_cases_first (cs : proof_cat list) : proof_cat list =
  List.stable_sort
    (fun c1 c2 ->
      let c1_is_ind = has_ihs c1 in
      let c2_is_ind = has_ihs c2 in
      if c1_is_ind && not c2_is_ind then
        1
      else if not c2_is_ind && c1_is_ind then
        -1
      else
        0)
    cs

(*
 * Search an inductive proof for a patch.
 * That is, break it into cases, and search those cases for patches.
 *
 * This does not yet handle nested inducted proofs.
 * It needs to hook back into search to do that.
 *
 * This does not yet handle the case when the inductive parameters
 * are lists of different lengths, and this currently only searches for patches
 * that are for changes in conclusions.
 *)
let search_for_patch_inductive search opts (d : (proof_cat * int) proof_diff) : candidates =
  let (o, nparams) = old_proof d in
  let (n, nparams_n) = new_proof d in
  if not (nparams = nparams_n) then
    give_up
  else
    zoom_map
      (fun d ->
        let assums = assumptions d in
        let old_cases = base_cases_first (split (old_proof d)) in
        let new_cases = base_cases_first (split (new_proof d)) in
        let ds = dest_cases (difference old_cases new_cases assums) in
        List.map (unshift_by nparams) (search_and_check_cases search opts ds))
      []
      id
      (fun d ->
        intro_common
          (Option.get
             (List.fold_right2
                (fun pm1 pm2 (d : proof_cat_diff option) ->
                  let e1 = map_ext id pm1 in
                  let e2 = map_ext id pm2 in
                  let assums = assumptions (Option.get d) in
                  if extensions_equal_assums e1 e2 assums then
                    intro_common (Option.get d)
                  else
                    intro (Option.get d))
                (params (old_proof d) nparams)
                (params (new_proof d) nparams)
                (Some d))))
      (difference o n (assumptions d))

(* --- General proof terms --- *)

(*
 * Check if a term applies the inductive hypothesis
 * This is naive for now
 *)
let applies_ih opts (d : goal_proof_diff) : bool =
  map_if
    (fun (t1, t2) -> isApp t1 && isApp t2)
    (fun (t1, t2) ->
      let (f1, args1) = destApp t1 in
      let (f2, args2) = destApp t2 in
      is_ind opts && same_length args1 args2 && isLambda f1 && isLambda f2)
    (always false)
    (proof_terms d)

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
  let search_ind = search_for_patch_inductive search in
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
