(* --- Recursive Differencers for Application --- *)

open Term
open Proofcatterms
open Proofdiff
open Candidates
open Searchopts
open Coqterms
open Differencers
open Collections
open Proofdifferencers
open Higherdifferencers
open Assumptions
open Cutlemma
open Specialization
open Zooming
open Printing
open Debruijn
open Filters

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
 * TODO: clean up
 *)
let diff_app diff_f diff_arg opts (d : goal_proof_diff) : candidates =
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
           filter_diff_cut (diff_map_flat (diff_rec diff_arg opts)) d_args_rev
      | ConclusionCase cut when isConstruct f_o && isConstruct f_n ->
         let diff_arg o d = if no_diff o d then give_up else diff_arg o d in
         filter_diff
           (fun args ->
             if Option.has_some cut then
               let args_lambdas = List.map (reconstruct_lambda env) args in
               filter_applies_cut env (Option.get cut) args_lambdas
             else
               args)
           (diff_map_flat (diff_rec diff_arg (set_change opts Conclusion)))
	   d_args
      | Hypothesis (_, _) ->
         let old_goal = fst (old_proof d) in
         let new_goal = fst (new_proof d) in
         let (g_o, g_n) = map_tuple context_term (old_goal, new_goal) in
         let goal_type = mkProd (Anonymous, g_n, shift g_o) in
         let filter_goal = filter_by_type env goal_type in
         let filter_diff_h diff = filter_diff filter_goal diff in
         let fs = filter_diff_h (diff_rec diff_f opts) d_f in
         if non_empty fs then
           fs
         else
           (* let d_args_rev = reverse d_args in *)
           filter_diff_h (diff_map_flat (diff_rec diff_arg opts)) d_args
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
 * For changes in constructors, hypotheses, or fixpoint cases, don't specialize.
 *)
let diff_app_ind diff_ind diff_arg opts (d : goal_proof_diff) : candidates =
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
    | (InductiveType (_, _)) | (Hypothesis (_, _)) ->
       f
    | FixpointCase ((_, _), cut) ->
       let env = context_env (fst (old_proof d)) in
       let filter_diff_cut diff = filter_diff (filter_cut env cut) diff in
       if non_empty f then
         f
       else
	 let diff_rec diff opts = diff_terms (diff opts) d opts in
	 let d_args = difference (Array.of_list args_o) (Array.of_list args_n) no_assumptions in
         let d_args_rev = reverse d_args in
         filter_diff_cut (diff_map_flat (diff_rec diff_arg opts)) d_args_rev
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
                (diff_map
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
