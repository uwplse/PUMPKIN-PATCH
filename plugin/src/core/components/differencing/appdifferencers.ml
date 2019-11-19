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
open Debruijn
open Filters
open Stateutils
open Convertibility
open Kindofchange
open Names
open Expansion
open Indutils
open Declarations
open Environ
open Funutils

(* --- Auxiliary functions (may move later) --- *)
       
(*
 * Update search goals and then recursively diff
 *)
let diff_update_goals diff opts assums envs terms goals terms_next =
  bind
    (update_search_goals opts envs terms goals envs terms_next)
    (fun (envs, terms, goals) -> diff assums envs terms goals)

(*
 * Lift give_up to a proof_differencer
 *)
let diff_give_up _ _ _ _ =
  ret give_up

(*
 * All convertible that places nicely with state
 *)
let all_convertible env =
  fold_tuple_state
    (forall2_state (fun t1 t2 sigma -> convertible env sigma t1 t2))

(*
 * Wrapper for specialization without reduction that ignores state
 * (since state is never used here)
 *)
let app env f args =
  snd (specialize_using specialize_no_reduce env f args Evd.empty)

(* --- Main functions --- *)
    
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
 *)
let diff_app diff_f diff_arg opts assums envs terms goals =
  let diff_rec diff opts assums terms_next =
    diff_update_goals (diff opts) opts assums envs terms goals terms_next
  in
  let chain_diff_app diff_f diff_args =
    try_chain_diffs [diff_f; diff_args] assums envs terms goals
  in
  let env = fst envs in
  match map_tuple kind terms with
  | (App (f_o, args_o), App (f_n, args_n)) when Array.length args_o = Array.length args_n ->
     let diff_f_rec = diff_rec diff_f in
     let diff_args_rec opts = diff_map_flat (diff_rec diff_arg opts) in
     let fs = (f_o, f_n) in
     let argss = map_tuple Array.to_list (args_o, args_n) in
     (match get_change opts with
      | InductiveType (_, _) ->
         diff_f_rec opts assums fs
      | FixpointCase ((_, _), cut) ->
         let diff_filter_cut diff terms_next assums _ _ _ =
           bind (diff opts assums terms_next) (filter_cut env cut)
         in
         chain_diff_app
           (diff_filter_cut diff_f_rec fs)
           (diff_filter_cut diff_args_rec (reverse argss))
      | ConclusionCase cut when isConstruct f_o && isConstruct f_n ->
         let opts = set_change opts Conclusion in
         let diff_filter_applies_cut diff terms_next =
           bind
             (diff opts assums terms_next)
             (fun args ->
               if Option.has_some cut then
                 filter_applies_cut
                   env
                   (Option.get cut)
                   (List.map (reconstruct_lambda env) args)
               else
                 ret args)
         in
         diff_filter_applies_cut
           (fun opts ->
             diff_map_flat
               (diff_rec
                  (fun opts ->
                    branch_diff (no_diff opts) diff_give_up (diff_arg opts))
                  opts))
           argss
      | Hypothesis (_, _) ->
         let goal_type = mkProd (Anonymous, snd goals, shift (fst goals)) in
         let filter_diff_h diff terms_next assums _ _ _ =
           bind
             (diff opts assums terms_next)
             (fun trms sigma -> filter_by_type goal_type env sigma trms)
         in
         chain_diff_app
           (filter_diff_h diff_f_rec fs)
           (filter_diff_h diff_args_rec argss)
      | Conclusion | Identity ->
         branch_state
           (all_convertible env)
           (fun _ ->
             let combine_app = combine_cartesian (app env) in
	     let args = Array.map (fun a_o -> [a_o]) args_o in
             bind
               (diff_f_rec opts assums fs)
               (fun fs -> ret (combine_app fs (combine_cartesian_append args))))
           (fun _ -> ret give_up)
           argss
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
let diff_app_ind diff_ind diff_arg opts assums envs terms goals sigma =
  let diff_rec diff opts assums terms_next =
    diff_update_goals (diff opts) opts assums envs terms goals terms_next
  in
  let sigma, elim_o = deconstruct_eliminator (fst envs) sigma (fst terms) in
  let sigma, elim_n = deconstruct_eliminator (snd envs) sigma (snd terms) in
  let env = fst envs in
  let final_args_o = elim_o.final_args in
  let final_args_n = elim_n.final_args in
  match get_change opts with
  | (InductiveType (_, _)) | (Hypothesis (_, _)) ->
     diff_ind opts assums envs (elim_o, elim_n) goals sigma
  | FixpointCase ((_, _), cut) ->
     let diff_filter_cut diff terms_next assums _ _ _ =
       bind (diff opts assums terms_next) (filter_cut env cut)
     in
     try_chain_diffs
       [(fun assums envs _ ->
           diff_ind opts assums envs (elim_o, elim_n));
        (diff_filter_cut
           (fun opts -> diff_map_flat (diff_rec diff_arg opts))
           (final_args_n, final_args_o))]
       assums
       envs
       terms
       goals
       sigma
  | _ ->
     if non_empty final_args_o then
       let m_arity = arity elim_o.p in
       let ind_args_o, _ = split_at m_arity final_args_o in
       let ind_args_n, _ = split_at m_arity final_args_n in
       if is_identity (get_change opts) then
         (* optimization *)
         bind
           (diff_ind opts assums envs (elim_o, elim_n) goals)
           (map_state
              (fun f -> 
	        let dummy_arg = mkRel 1 in
                let f_args = Array.of_list ind_args_o in
	        ret (app env (app env f f_args) (Array.make 1 dummy_arg))))
           sigma
       else
         (* proof differencing *)
         let diff_apply diff arg_n opts assums envs terms goals =
           bind
             (diff opts assums envs terms goals)
             (map_state
                (fun p -> ret (app env p (Array.make 1 arg_n))))
         in
         bind
           (diff_ind opts assums envs (elim_o, elim_n) goals)
           (fun f ->
             bind
               (diff_map
		  (fun assums (arg_o, arg_n) ->                
                    diff_update_goals
                      (diff_apply diff_arg arg_n opts)
                      opts
                      assums
                      envs
                      terms
                      goals
                      (arg_o, arg_n))
                  assums
                  (ind_args_n, ind_args_o))
               (fun argss ->
                 let argss = combine_cartesian_append (Array.of_list argss) in
                 ret (combine_cartesian (app env) f argss)))
           sigma
     else
       diff_ind opts assums envs (elim_o, elim_n) goals sigma
