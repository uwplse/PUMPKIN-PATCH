(* --- Differencing Component --- *)

open Proofcat
open Proofcatterms
open Searchopts
open Proofdiff
open Assumptions
open Term
open Environ
open Coqterms
open Debruijn
open Reducers
open Candidates
open Collections
open Coqenvs
open Cutlemma
open Kindofchange
open Printing
open Specialization
open Zooming
open Evaluation
open Abstraction
open Utilities
open Differencers
open Proofdifferencers

(* --- Recursive differencing --- *)

(*
 * Try to difference with one differencer
 * If that fails, then try the next one
 *)
let rec try_chain_diffs diffs d =
  match diffs with
  | diff_h :: diff_t ->
     let cs = diff_h d in
     if non_empty cs then
       cs
     else
       try_chain_diffs diff_t d
  | _ ->
     give_up

(*
 * Try to reduce and then diff
 * If reducing does not change the term, then give_up to prevent
 * inifinite recursion
 *)
let diff_reduced diff d =
  let (o, n) = proof_terms d in
  let d_red = reduce_diff reduce_term d in
  let (o_red, n_red) = proof_terms d_red in
  if not ((eq_constr o o_red) && (eq_constr n n_red)) then
    diff d_red
  else
    give_up

(*
 * Convert a differencing function that takes a diff into one between two terms
 *
 * In other words, take an old diff d with assumptions that still hold, and:
 * 1. Update the terms and goals of the diff d to use those terms
 * 2. Apply the differencing function to the new diff
 *)
let diff_terms (diff : proof_differencer) d opts d_t : candidates =
  diff (update_terms_goals opts (old_proof d_t) (new_proof d_t) d)

(*
 * Using some term differencer, recursively difference the arguments
 * Return a single list of all of the differences flattened, which
 * does not correspond to each argument
 *)
let diff_args_flat (diff : term_differencer) d_args =
  let assums = assumptions d_args in
  let diff_arg a_o a_n = diff (difference a_o a_n assums) in
  apply_to_arrays (flat_map2 diff_arg) (old_proof d_args) (new_proof d_args)

(*
 * Same, but don't flatten
 *)
let diff_args (diff : term_differencer) d_args =
  let assums = assumptions d_args in
  let diff_arg a_o a_n = diff (difference a_o a_n assums) in
  apply_to_arrays (List.map2 diff_arg) (old_proof d_args) (new_proof d_args)

(*
 * Apply some differencing function
 * Filter the result using the supplied modifier
 *)
let filter_diff filter (diff : ('a, 'b) differencer) d : 'b =
  filter (diff d)

(*
 * Given a search function and a difference between terms,
 * if the terms are applications (f args) and (f' args'),
 * then recursively diff the functions and/or arguments.
 *
 * This function currently exists to workaround types that aren't properly
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
 *
 * TODO: clean up, and clean input types
 *)
let diff_app opts diff_f diff_arg (d : goal_proof_diff) : candidates =
  let (_, env) = fst (old_proof (dest_goals d)) in
  match kinds_of_terms (proof_terms d) with
  | (App (f_o, args_o), App (f_n, args_n)) when same_length args_o args_n ->
     let diff_rec diff opts = diff_terms (diff opts) d opts in
     let d_f = difference f_o f_n no_assumptions in
     let d_args = difference args_o args_n no_assumptions in
     (match get_change opts with
      | InductiveType (_, _) ->
         diff_rec diff_f opts d_f
      | FixpointCase ((_, _), cut) ->
         let filter_diff_cut diff = filter_diff (filter_cut env cut) diff in
         let fs = filter_diff_cut (diff_rec diff_f opts) d_f in
         if non_empty fs then
           fs
         else
           let d_args_rev = reverse d_args in
           filter_diff_cut (diff_args_flat (diff_rec diff_arg opts)) d_args_rev
      | ConclusionCase cut when isConstruct f_o && isConstruct f_n ->
         let diff_arg o d = if no_diff o d then give_up else diff_arg o d in
         filter_diff
           (fun args ->
             if Option.has_some cut then
               let args_lambdas = List.map (reconstruct_lambda env) args in
               filter_applies_cut env (Option.get cut) args_lambdas
             else
               args)
           (diff_args_flat (diff_rec diff_arg (set_change opts Conclusion)))
	   d_args
      | Conclusion ->
         if args_convertible env args_o args_n then
           let specialize = specialize_using specialize_no_reduce env in
           let combine_app = combine_cartesian specialize in
	   let fs = diff_rec diff_f opts d_f in
	   let args = Array.map (fun a_o -> [a_o]) args_o in
           combine_app fs (combine_cartesian_append args)
         else
           give_up)
  | _ ->
     give_up

(*
 * Search an application of an induction principle.
 * Basically, use the normal induction differencing function,
 * then specialize to any final arguments.
 *
 * For changes in constructors or fixpoint cases, don't specialize.
 *)
let diff_app_ind opts diff_ind diff_arg (d : goal_proof_diff) : candidates =
  let d_proofs = erase_goals d in
  let o = old_proof d_proofs in
  let n = new_proof d_proofs in
  let d_ind = difference (o, 0, []) (n, 0, []) (assumptions d) in
  let d_opt = zoom_same_hypos d_ind in
  if Option.has_some d_opt then
    let d_zoom = Option.get d_opt in
    let assums = assumptions d_zoom in
    let (o, npms_old, args_o) = old_proof d_zoom in
    let (n, npms_new, args_n) = new_proof d_zoom in
    let f = diff_ind opts (difference (o, npms_old) (n, npms_new) assums) in
    match get_change opts with
    | InductiveType (_, _) ->
       f
    | FixpointCase ((_, _), _) ->
       f
    | _ ->
       if non_empty args_o then
         let env_o = context_env (fst (old_proof d)) in
         let (_, prop_trm_ext, _) = prop o npms_old in
         let prop_trm = ext_term prop_trm_ext in
         let rec prop_arity p =
           match kind_of_term p with
           | Lambda (_, _, b) ->
              1 + prop_arity b
           | Prod (_, _, b) ->
              1 + prop_arity b
           | _ ->
              0
         in
         let arity = prop_arity prop_trm in
         let specialize = specialize_using specialize_no_reduce env_o in
         let final_args_o = Array.of_list (fst (split_at arity args_o)) in
         let final_args_n = Array.of_list (fst (split_at arity args_n)) in
         let d_args = difference final_args_n final_args_o no_assumptions in
         combine_cartesian
           specialize
           f
           (combine_cartesian_append
             (Array.of_list
                (diff_args
                   (fun d_a ->
                     let arg_n = new_proof d_a in
                     let apply p = specialize p (singleton_array arg_n) in
                     let diff_apply = filter_diff (List.map apply) in
                     diff_terms (diff_apply (diff_arg opts)) d opts d_a)
                   d_args)))
       else
         f
  else
    give_up

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
let rec diff_case abstract diff (d : goal_case_diff) : candidates =
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
          diff_case abstract diff d_t
      with _ ->
        diff_case abstract diff d_t)
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
let diff_ind_case opts diff (d : goal_case_diff) : candidates =
  diff_case (abstract_case opts d) diff d

(*
 * Search a case of a difference in proof categories.
 * Return a patch if we find one.
 *
 * This breaks it up into arrows and then searches those
 * in the order of the sort function.
 *)
let diff_sort_ind_case opts sort diff (d : proof_cat_diff) : candidates =
  let o = old_proof d in
  let n = new_proof d in
  let ms_o = morphisms o in
  let ms_n = morphisms n in
  let d_ms = difference ms_o ms_n (assumptions d) in
  diff_ind_case
    opts
    (diff opts)
    (reset_case_goals
       opts
       (map_diffs
          (fun (o, ms) -> (terminal o, ms))
          (always (update_case_assums d_ms))
          (add_to_diff d (sort o ms_o) (sort n ms_n))))

(*
 * Base case: Prefer arrows later in the proof
 *)
let diff_base_case opts diff (d : proof_cat_diff) : candidates =
  let sort _ ms = List.rev ms in
  diff_sort_ind_case (set_is_ind opts false) sort diff d

(*
 * Inductive case: Prefer arrows closest to an IH,
 * and in a tie, prefer arrows that are later.
 *
 * There currently may not be a guarantee that the two
 * arrows are traversed in exactly the same order for each proof.
 * If there is a bug in this, this may be why.
 *)
let diff_inductive_case opts diff (d : proof_cat_diff) : candidates =
  let sort c ms = List.stable_sort (closer_to_ih c (find_ihs c)) ms in
  diff_sort_ind_case (set_is_ind opts true) sort diff d

(*
 * Depending on whether a proof has inductive hypotheses, difference
 * it treating it either like a base case (no inductive hypotheses)
 * or an inductive case (some inductive hypotheses).
 *)
let diff_base_or_inductive_case opts diff (d : proof_cat_diff) : candidates =
  let o = old_proof d in
  if has_ihs o then
    diff_inductive_case opts diff d
  else
    diff_base_case opts diff d

(*
 * Diff a case, then adjust the patch so it type-checks
 * in the original envionment.
 *
 * If there is a bug here, then the offset we unshift by may not generalize
 * for all cases.
 *)
let diff_and_unshift_case opts diff (d : proof_cat_diff) : candidates =
  let d_exp = expand_constrs d in
  List.map
    (fun trm ->
      if is_conclusion (get_change opts) then
        unshift_by (List.length (morphisms (old_proof d_exp))) trm
      else
        trm)
    (diff_base_or_inductive_case opts diff d_exp)

(*
 * Search in a diff that has been broken up into different cases.
 * That is, search the base case, inductive case, and so on separately.
 *
 * For now, we only return the first patch we find.
 * We may want to return more later.
 *)
let rec diff_ind_cases opts diff (ds : proof_cat_diff list) : candidates =
  match ds with
  | d :: tl ->
     let patches = diff_and_unshift_case opts diff d in
     if non_empty patches then
       patches
     else
       diff_ind_cases opts diff tl
  | [] ->
     []

(*
 * Search an inductive proof for a patch.
 * That is, break it into cases, and search those cases for patches.
 *
 * This does not yet handle nested inducted proofs.
 *
 * This does not yet handle the case when the inductive parameters
 * are lists of different lengths, or where there is a change in hypothesis.
 *)
let diff_inductive opts diff (d : (proof_cat * int) proof_diff) : candidates =
  let (o, nparams_o) = old_proof d in
  let (n, nparams_n) = new_proof d in
  if not (nparams_o = nparams_n) then
    give_up
  else
    zoom_map
      (fun d ->
        let d_sorted = map_diffs (fun c -> base_cases_first (split c)) id d in
        let ds = dest_cases d_sorted in
        List.map (unshift_by nparams_o) (diff_ind_cases opts diff ds))
      []
      id
      (intro_params nparams_o)
      (difference o n (assumptions d))

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
 * 6c. When 6b doesn't produce anything, try reducing the diff and calling
 *    recursively. (Support for this is preliminary.)
 *)
let rec diff (opts : options) (d : goal_proof_diff) : candidates =
  let d = reduce_letin (reduce_casts d) in
  let diff_ind = fun opts -> diff_inductive opts diff in
  if no_diff opts d then
    (*1*) identity_candidates d
  else if induct_over_same_h (same_h opts) d then
    try_chain_diffs
      [(diff_app_ind opts diff_ind diff); (* 2a *)
       (find_difference opts)]            (* 2b *)
      d
  else if applies_ih opts d then
    (*3*) diff_app opts diff diff (reduce_trim_ihs d)
  else
    match kinds_of_terms (proof_terms d) with
    | (Lambda (n_o, t_o, b_o), Lambda (_, t_n, b_n)) ->
       if no_diff opts (eval_with_terms t_o t_n d) then
         (*4*) zoom_wrap_lambda (to_search_function diff opts d) n_o t_o d
       else
         if is_ind opts || not (is_conclusion (get_change opts)) then
           (*5*) zoom_unshift (to_search_function diff opts d) d
         else
           give_up
    | _ ->
       if is_app opts d then
         try_chain_diffs
           [(find_difference opts);     (* 6a *)
            (diff_app opts diff diff);  (* 6b *)
            (diff_reduced (diff opts))] (* 6c *)
           d
       else
         give_up

(* --- Differencing of types & terms --- *)

(*
 * Gets the change in the case of a fixpoint branch.
 * These are the goals for abstraction.
 * Since semantic differencing doesn't have a good model of fixpoints yet,
 * this is a little complicated, and currently works directly over
 * the old representation. It's also the only function so far
 * to delta-reduce, which we can learn from.
 *
 * But basically this detects a change in a fixpoint case and
 * just is super preliminary.
 * After the prototype we should model fixpoints better.
 *)
let rec get_goal_fix env (d : types proof_diff) : candidates =
  let old_term = old_proof d in
  let new_term = new_proof d in
  let assums = assumptions d in
  if eq_constr old_term new_term then
    give_up
  else
    match kinds_of_terms (old_term, new_term) with
    | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) when convertible env t1 t2 ->
       List.map
         (fun c -> mkProd (n1, t1, c))
         (get_goal_fix (push_rel (n1, None, t1) env) (difference b1 b2 assums))
    | _ ->
       let reduce_hd = reduce_unfold_whd env in
       let rec get_goal_reduced d =
         let red_old = reduce_hd (old_proof d) in
         let red_new = reduce_hd (new_proof d) in
         match kinds_of_terms (red_old, red_new) with
         | (App (f1, args1), App (f2, args2)) when eq_constr f1 f2 ->
            let d_args = difference args1 args2 no_assumptions in
            diff_args_flat get_goal_reduced d_args
         | _ when not (eq_constr red_old red_new) ->
            [reduce_unfold env (mkProd (Anonymous, red_old, shift red_new))]
         | _ ->
            give_up
       in get_goal_reduced (difference old_term new_term no_assumptions)

(* Same as the above, but at the top-level for the fixpoint case *)
let rec diff_fix_case env (d : types proof_diff) : candidates =
  let old_term = old_proof d in
  let new_term = new_proof d in
  let assums = assumptions d in
  let conv = convertible env in
  match kinds_of_terms (old_term, new_term) with
  | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) when conv t1 t2 ->
     diff_fix_case (push_rel (n1, None, t1) env) (difference b1 b2 assums)
  | (Case (_, ct1, m1, bs1), Case (_, ct2, m2, bs2)) when conv m1 m2  ->
     if same_length bs1 bs2 then
       let env_m = push_rel (Anonymous, None, m1) env in
       let diff_bs = diff_args_flat (get_goal_fix env_m) in
       List.map
         unshift
         (List.append
            (diff_bs (difference bs1 bs2 assums))
            (diff_bs (difference bs2 bs1 assums)))
     else
       give_up
  | _ ->
     give_up

(* Same as above, for all of the cases of a fixpoint *)
let diff_fix_cases env (d : types proof_diff) : candidates =
  let old_term = unwrap_definition env (old_proof d) in
  let new_term = unwrap_definition env (new_proof d) in
  let assums = assumptions d in
  match kinds_of_terms (old_term, new_term) with
  | (Fix ((_, i), (nso, tso, dso)), Fix ((_, j), (_, tsn, dsn))) when i = j ->
    if args_convertible env tso tsn then
      let env_fix = push_rel_context (bindings_for_fix nso tso) env in
      let d_ds = difference dso dsn assums in
      let ds = diff_args_flat (diff_fix_case env_fix) d_ds in
      let lambdas = List.map (reconstruct_lambda env_fix) ds in
      let apps =
        List.map
          (fun t -> mkApp (t, singleton_array new_term))
          lambdas
      in unique eq_constr (reduce_all reduce_term env apps)
    else
      failwith "Cannot infer goals for generalizing change in definition"
  | _ ->
     failwith "Not a fixpoint"

(* --- Top-level differencer --- *)

(* Given a configuration, return the appropriate differencer *)
let get_differencer (opts : options) =
  let should_reduce = is_inductive_type (get_change opts) in
  if should_reduce then
    (fun d -> diff opts (reduce_diff reduce_term d))
  else
    diff opts
