(* --- Recursive Differencers for Application --- *)

open Utilities
open Constr
open Proofcatterms
open Proofdiff
open Candidates
open Searchopts
open Evd
open Proofdifferencers
open Higherdifferencers
open Assumptions
open Cutlemma
open Specialization
open Zooming
open Catzooming
open Debruijn
open Filters
open Stateutils
open Convertibility
open Kindofchange

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
 * 4. When searching for a change in conclusions (or doing optimization),
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
let diff_app diff_f diff_arg opts d =
  let ((goal_o, _), (_, _), _) = d in
  let env = snd (dest_context_term goal_o) in
  match map_tuple kind (proof_terms d) with
  | (App (f_o, args_o), App (f_n, args_n)) when Array.length args_o = Array.length args_n ->
     let diff_rec diff opts ts = diff_terms (diff opts) d opts ts in
     let d_f = f_o, f_n, no_assumptions in
     let d_args = args_o, args_n, no_assumptions in
     (match get_change opts with
      | InductiveType (_, _) ->
         diff_rec diff_f opts d_f
      | FixpointCase ((_, _), cut) ->
         let filter_diff_cut diff d = filter_diff (filter_cut env cut) diff d in
         bind
           (filter_diff_cut (diff_rec diff_f opts) d_f)
           (fun fs ->
             if non_empty fs then
               ret fs
             else
               filter_diff_cut
                 (diff_map_flat (diff_rec diff_arg opts))
                 (args_n, args_o, no_assumptions))
      | ConclusionCase cut when isConstruct f_o && isConstruct f_n ->
         filter_diff
           (fun args ->
             if Option.has_some cut then
               let args_lambdas = List.map (reconstruct_lambda env) args in
               filter_applies_cut env (Option.get cut) args_lambdas
             else
               ret args)
           (diff_map_flat
              (diff_rec
                 (fun opts d ->
                   branch_state
                     (fun ((goal_o, o), (goal_n, n), assums) ->
                       let goals = map_tuple dest_context_term (goal_o, goal_n) in
                       let envs = map_tuple snd goals in
                       let goals = map_tuple fst goals in
                       let terms = map_tuple only_extension_as_term (o, n) in
                       no_diff opts assums envs terms goals)
                     (fun _ -> ret give_up)
                     (diff_arg opts)
                     d)
                 (set_change opts Conclusion)))
	   d_args
      | Hypothesis (_, _) ->
         let ((old_goal, _), (new_goal, _), _) = d in
         let (g_o, g_n) = map_tuple context_term (old_goal, new_goal) in
         let goal_type = mkProd (Names.Name.Anonymous, g_n, shift g_o) in
         let filter_goal trms evd = filter_by_type goal_type env evd trms in
         let filter_diff_h diff = filter_diff filter_goal diff in
         bind
           (filter_diff_h (diff_rec diff_f opts) d_f)
           (fun fs ->
             if non_empty fs then
               ret fs
             else
               filter_diff_h (diff_map_flat (diff_rec diff_arg opts)) d_args)
      | Conclusion | Identity ->
         branch_state
           (fun (args_o, args_n) ->
             forall2_state
               (fun t1 t2 sigma -> convertible env sigma t1 t2)
               (Array.to_list args_o)
               (Array.to_list args_n))
           (fun (args_o, args_n) ->
             let app f args =
               snd (specialize_using specialize_no_reduce env f args Evd.empty)
             in
             let combine_app = combine_cartesian app in
	     let args = Array.map (fun a_o -> [a_o]) args_o in
             bind
               (diff_rec diff_f opts d_f)
               (fun fs -> ret (combine_app fs (combine_cartesian_append args))))
           (fun _ -> ret give_up)
           (args_o, args_n)
      | _ ->
         ret give_up)
  | _ ->
     ret give_up

(*
 * Search an application of an induction principle.
 * Basically, use the normal induction differencing function,
 * then specialize to any final arguments.
 *
 * For changes in constructors, hypotheses, or fixpoint cases, don't specialize.
 *)
let diff_app_ind diff_ind diff_arg opts d =
  let ((_, o), (_, n), assums) = d in
  let d_ind = (o, 0, []), (n, 0, []), assums in
  bind
    (zoom_same_hypos d_ind)
    (fun d_opt sigma ->
      if Option.has_some d_opt then
        let ((o, npms_o, as_o), (n, npms_n, as_n), assums) = Option.get d_opt in
        let sigma_f, f  = diff_ind opts ((o, npms_o), (n, npms_n), assums) sigma in
        match get_change opts with
        | (InductiveType (_, _)) | (Hypothesis (_, _)) ->
           sigma_f, f
        | FixpointCase ((_, _), cut) ->
           let ((goal_o, _), (_, _), _) = d in
           let env = context_env goal_o in
           let filter_diff_cut diff d = filter_diff (filter_cut env cut) diff d in
           if non_empty f then
             sigma_f, f
           else
             (* Note that state is relevant here; don't use sigma_f *)
	     let diff_rec diff opts = diff_terms (diff opts) d opts in
	     let as_o, as_n = map_tuple Array.of_list (as_o, as_n) in
             let d_args_rev = as_n, as_o, no_assumptions in
             filter_diff_cut (diff_map_flat (diff_rec diff_arg opts)) d_args_rev sigma
        | _ ->
           if non_empty as_o then
             let ((goal_o, _), (_, _), _) = d in
             let env_o = context_env goal_o in
             let _, (_, prop_trm_ext, _) = prop o npms_o sigma in
             let prop_trm = ext_term prop_trm_ext in
             let rec prop_arity p =
               match kind p with
               | Lambda (_, _, b) ->
                  1 + prop_arity b
               | Prod (_, _, b) ->
                  1 + prop_arity b
               | _ ->
                  0
             in
             let arity = prop_arity prop_trm in
             let app f args = snd (specialize_using specialize_no_reduce env_o f args Evd.empty) in
             let final_args_o = Array.of_list (fst (split_at arity as_o)) in
	     if is_identity (get_change opts) then (* TODO explain *)
	       sigma, List.map 
	                (fun f -> 
	                  let dummy_arg = mkRel 1 in
	                  app (app f final_args_o) (Array.make 1 dummy_arg)) 
	                f
	     else
               let final_args_n = Array.of_list (fst (split_at arity as_n)) in
               let d_args = final_args_n, final_args_o, no_assumptions in
	       let sigma, args =
                 Util.on_snd
	           Array.of_list
                   (diff_map
		      (fun d_a ->
                        let (_, arg_n, _) = d_a in
                        let apply p = ret (app p (Array.make 1 arg_n)) in
                        let diff_apply = filter_diff (map_state apply) in
                        diff_terms (diff_apply (diff_arg opts)) d opts d_a)
                      d_args
                      sigma)
	       in sigma, combine_cartesian app f (combine_cartesian_append args)
           else
             sigma_f, f
      else
        sigma, give_up)
