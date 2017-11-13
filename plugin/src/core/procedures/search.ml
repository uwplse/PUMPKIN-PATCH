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

(* --- Application --- *)

(*
 * Given a search function and a difference between terms,
 * if the terms are applications (f args) and (f' args'),
 * then recursively search the difference in functions and/or arguments.
 *
 * This function mostly exists to workaround types that aren't properly
 * modeled yet, like nested induction and constructors, or
 * searching for patches that factor through some cut lemma
 * which the user has provided (because this is a prototype and
 * semantic differencing doesn't model everything yet).
 *
 * Heuristics explained:
 *
 * 1. When searching for a change in a constructor of an inductive type,
 *    just search the difference in functions.
 *    Don't try to specialize the result to any arguments.
 * 2. When searching for a change in a fixpoint case,
 *    try to find the lemma the user cut by.
 *    Try this both in the difference of functions (forwards)
 *    and in the difference of arguments (backwards).
 * 3. When searching for a change in arguments to a constructor,
 *    search for a change in conclusions to the arguments
 *    when the function is a constructor. If the user has
 *    cut by some lemma, then filter by that type,
 *    otherwise just return the result.
 * 4. When searching for a change in conclusions,
 *    search the difference in functions and apply to the old arguments.
 *    For now, we just require that the arguments haven't changed.
 *    Ideally, we should search (f_o -> f_n) and
 *    (map2 (a_n -> a_o) args_o args_n) applied to each arg_o,
 *    but the latter hasn't been necessary ever, so we don't do it for now.
 *
 * This will still fail to find patches in many cases.
 * We need to improve semantic differencing for those cases,
 * For example, if one application passes through an intermediate lemma
 * but the other doesn't, this function has no clue what to do.
 *)
let search_app search_f search_arg opts (d : goal_proof_diff) : candidates =
  let (_, env) = fst (old_proof (dest_goals d)) in
  match kinds_of_terms (proof_terms d) with
  | (App (f_o, args_o), App (f_n, args_n)) when same_length args_o args_n ->
     let d_f = difference f_o f_n no_assumptions in
     let d_args = difference args_o args_n no_assumptions in
     (match get_change opts with
      | InductiveType (_, _) ->
         diff_terms (search_f opts) d opts d_f
      | FixpointCase ((_, _), cut) ->
         let filter = filter_cut env cut in
         let fs = modify_diff (diff_terms (search_f opts) d opts) filter d_f in
         if non_empty fs then
           fs
         else
           modify_diff
             (diff_args (diff_terms (search_arg opts) (reverse d) opts))
             filter
             (reverse d_args)
      | ConclusionCase cut when isConstruct f_o && isConstruct f_n ->
         let opts = set_change opts Conclusion in
         let args =
           diff_args
             (diff_terms
                (map_if (no_diff opts) (always give_up) (search_arg opts))
                d
                opts)
	     d_args
         in
         if Option.has_some cut then
           let args_lambdas = List.map (reconstruct_lambda env) args in
           filter_applies_cut env (Option.get cut) args_lambdas
         else
           args
      | Conclusion ->
         if args_convertible env args_o args_n then
           let specialize = specialize_using specialize_no_reduce env in
           let combine_app = combine_cartesian specialize in
	   let f = search_f opts (update_terms_goals opts f_o f_n d) in
	   let args = Array.map (fun a_o -> [a_o]) args_o in
           combine_app f (combine_cartesian_append args)
         else
           give_up)
  | _ ->
     give_up

(*
 * After doing induction, search the difference in final arguments
 * That we, differencing can detect the final arguments to apply to
 *
 * Right now, this is limiting. It does actually let you apply
 * to different final arguments, (it will recursively search
 * the difference in those arguments), but it assumes that there is only
 * one argument the property applies to.
 *
 * So, for example, the conclusion of the nat induction principle is:
 *   forall (n : nat), P n
 *
 * This looks for that n once it finds the difference in P, so it
 * can tell specialization what to do. But it doesn't handle
 * induction principles where the conclusion is something like:
 *   forall t1 t2, P t1 t2
 *
 * The correct way to fix this when we make semantic differencing
 * better is to detect how many arguments the conclusion of the induction
 * principle takes, and only look that far. Because we want to specialize
 * by that argument, but we don't want to specialize by extra arguments
 * that show up afterward, like hypothesis. The example in the paper
 * in Section 3 is a case where you can see an extra argument we don't
 * want to specialize by.
 *)
let diff_final opts search_arg env_o env_n args_o args_n d =
  let final_arg_o = List.hd args_o in
  let final_arg_n = List.hd args_n in
  combine_cartesian_append
    (Array.of_list
       (List.map2
          (fun arg_o arg_n ->
            let a_o = eval_proof env_o arg_o in
            let a_n = eval_proof env_n arg_n in
            let d = add_goals (difference a_n a_o (assumptions d)) in
            let specialize = specialize_using specialize_no_reduce env_o in
            List.map
              (fun p -> specialize p (singleton_array arg_o))
              (search_arg opts d))
          ([final_arg_o])
          ([final_arg_n])))

(*
 * Search an application of an induction principle.
 * Basically, use the normal induction differencing function,
 * then specialize to any final arguments (the reduction step
 * happens later for now).
 *
 * For changes in constructors or fixpoint cases, don't specialize.
 *)
let search_app_ind search_ind search_arg opts d : candidates =
  let d_proofs = erase_goals d in
  let o = old_proof d_proofs in
  let n = new_proof d_proofs in
  let d_ind = difference (o, 0, []) (n, 0, []) (assumptions d) in
  let d_opt = zoom_same_hypos d_ind in
  if Option.has_some d_opt then
    let d_zoom = Option.get d_opt in
    let assums = assumptions d_zoom in
    let (o, npms_old, final_args_old) = old_proof d_zoom in
    let (n, npms_new, final_args_new) = new_proof d_zoom in
    let env_o = context_env (fst (old_proof d)) in
    let env_n = context_env (fst (new_proof d)) in
    let f = search_ind opts (difference (o, npms_old) (n, npms_new) assums) in
    match get_change opts with
    | InductiveType (_, _) ->
       f
    | FixpointCase ((_, _), _) ->
       f
    | _ ->
       if non_empty final_args_old then
         let args_o = final_args_old in
         let args_n = final_args_new in
         let args = diff_final opts search_arg env_o env_n args_o args_n d in
         let specialize = specialize_using specialize_no_reduce env_o in
         combine_cartesian specialize f args
       else
         f
  else
    give_up

(* Given a term, trim off the IH, assuming it's an application *)
let trim_ih (trm : types) : types =
  assert (isApp trm);
  let (f, args) = destApp trm in
  let args_trim = Array.sub args 0 ((Array.length args) - 1) in
  mkApp (f, args_trim)

(* Given a diff, trim off the IHs, assuming the terms are applications *)
let trim_ihs (d : goal_proof_diff) : goal_proof_diff =
  let (old_term, new_term) = map_tuple trim_ih (proof_terms d) in
  eval_with_terms old_term new_term d

(* --- Casts --- *)

(* Given a difference in proofs, trim down any casts and get the terms *)
let rec erase_casts (d : goal_proof_diff) : goal_proof_diff =
  match kinds_of_terms (proof_terms d) with
  | (Cast (t, _, _), _) ->
     erase_casts (eval_with_old_term t d)
  | (_, Cast (t, _, _)) ->
     erase_casts (eval_with_new_term t d)
  | _ ->
     d

(* --- LetIn --- *)

(* Given a difference in proofs, substitute the head let ins *)
let simplify_letin (d : goal_proof_diff) : goal_proof_diff =
  let (o, n) = proof_terms d in
  if isLetIn o || isLetIn n then
    let d_dest = dest_goals d in
    let ((_, old_env), _) = old_proof d_dest in
    let ((_, new_env), _) = new_proof d_dest in
    let o' = reduce_whd_if_let_in old_env o in
    let n' = reduce_whd_if_let_in new_env n in
    eval_with_terms o' n' d
  else
    d

(* --- Induction --- *)

(*
 * Given an ordered pair of lists of arrows to explore in the base case,
 * search the difference between each one.
 *
 * Stop as soon as we find a patch and return any of the patches.
 *
 * For now, we don't combine these in any way, and just look at the
 * difference between each pair, but without changing the goal type.
 * In the future we may want to be smarter about this.
 * All of the benchmarks so far work only with head, so it's unclear
 * what the recursive case should do so far. It might even be better
 * if it's just None like it used to be. Let's see where benchmarks
 * take us.
 *
 * The recursive call means that sometimes we'll end up with non-terms,
 * like the IHs, which not only can't be patches but will error
 * when we try to look. We should eliminate those from the list
 * before calling this.
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
let rec search_case_paths search opts (d : goal_case_diff) : types option =
  match diff_proofs d with
  | ((h1 :: t1), (h2 :: t2)) ->
     let d_goal = erase_proofs d in
     let d_t = add_to_diff d_goal t1 t2 in
     let ((_, env), _) = old_proof (dest_goals d) in
     (try
        let c1 = eval_proof_arrow h1 in
        let c2 = eval_proof_arrow h2 in
        let cs = search opts (add_to_diff d_goal c1 c2) in
        if non_empty cs then
          let candidate = List.hd cs in
          match get_change opts with
          | InductiveType (_, _) ->
             Some candidate
          | FixpointCase ((_, _), cut) when are_cut env cut cs ->
             Some candidate
          | _ ->
             let lcs = try_abstract_inductive d_goal cs in
             if non_empty lcs then
               Some (List.hd lcs)
             else
               search_case_paths search opts d_t
        else
          search_case_paths search opts d_t
      with _ ->
        search_case_paths search opts d_t)
  | (_, _) ->
     None

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
let search_case search opts sort (d : proof_cat_diff) : types option =
  let o = old_proof d in
  let n = new_proof d in
  let ms_o = morphisms o in
  let ms_n = morphisms n in
  search_case_paths
    search
    opts
    (reset_case_goals
       opts
       (map_diffs
          (fun (o, ms) -> (terminal o, ms))
          (always (update_case_assums d ms_o ms_n))
          (add_to_diff d (sort o ms_o) (sort n ms_n))))

(*
 * Base case: Prefer arrows later in the proof
 *)
let search_base_case search opts (d : proof_cat_diff) : types option =
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
let search_inductive_case search opts (d : proof_cat_diff) : types option =
  let sort c ms = List.stable_sort (closer_to_ih c (find_ihs c)) ms in
  search_case search (set_is_ind opts true) sort d

(*
 * Search in a case, then adjust the patch so it type-checks
 * in the original envionment.
 *
 * If there is a bug here, then the unshift number may not generalize
 * for all cases.
 *)
let search_and_check_case search opts (d : proof_cat_diff) : types option =
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
  Option.map
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
     let patch = search_and_check_case search opts d in
     if Option.has_some patch then
       [Option.get patch]
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
  let d = erase_casts d in
  let d = simplify_letin d in
  let search_ind = search_for_patch_inductive search in
  if no_diff opts d then
    (*1*) identity_candidates d
  else if induct_over_same_h (same_h opts) d then
    (*2a*) let patches = search_app_ind search_ind search opts d in
    if non_empty patches then
      patches
    else
      (*2b*) find_difference opts d
  else if applies_ih opts d then
    (*3*) search_app search search opts (trim_ihs d)
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
           (*6b*) let patches = search_app search search opts d in
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
