(* --- Differencing of Inductive Proofs --- *)

open Utilities
open Constr
open Proofcat
open Proofcatterms
open Proofdiff
open Candidates
open Evaluation
open Catzooming
open Zooming
open Debruijn
open Kindofchange
open Searchopts
open Abstraction
open Expansion
open Environ
open Evd
open Higherdifferencers
open Stateutils
open Envutils
open Indutils

(* --- Cases --- *)

(*
 * Given an ordered pair of lists of subterms to explore in a case of an
 * inductive proof, difference each one (using diff).
 * As soon as we find candidates that can be properly abstracted
 * (using abstract), return those. Otherwise, recurse.
 *
 * For now, we don't combine these in any way, and just look at the
 * difference between each pair, but without changing the goal type.
 * In the future we may want to be smarter about this.
 * To improve this, we need benchmarks for which the head is not the patch,
 * but another subterm is.
 *
 * TODO just use lambdas like a normal person
 *)
let rec diff_case abstract diff assums envs termss goals =
  match termss with
  | ((term_o :: tl_o), (term_n :: tl_n)) ->
     try_chain_diffs
       [(fun assums envs terms goals sigma ->
           try
             bind (diff assums envs terms goals) abstract sigma
           with _ ->
             ret [] sigma);
        (fun assums envs _ ->
          diff_case abstract diff assums envs (tl_o, tl_n))]
       assums
       envs
       (term_o, term_n)
       goals
  | _ ->
     ret give_up

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
let diff_ind_case opts diff assums envs termss goals =
  diff_case (abstract_case opts assums envs goals) diff assums envs termss goals
                
(*
 * Search a case of a difference in proof categories.
 * Return a patch if we find one.
 *
 * This breaks it up into arrows and then searches those
 * in reverse order (this used to take a sorting function, but sorting
 * had no impact on performance).
 *
 * TODO be a normal person and use lambdas here
 * TODO clean unnecessary args here (e.g. are any of the envs redundant?
 * is anything just not referenced? lots going on)
 *)
let break_diff_ind_case opts diff assums envs_old goals_old envs goals c_envs c_terms c_goals sigma =
  let sigma, assums = update_case_assums assums c_envs c_goals sigma in
  let envs, goals = reset_case_goals opts envs_old goals_old envs goals in
  if is_hypothesis (get_change opts) then
    (* deal with the extra hypothesis *)
    let num_new_rels = new_rels2 (fst envs) (fst envs_old) in
    bind
      (diff_ind_case opts (diff opts) assums envs c_terms goals)
      (fun cs -> ret (List.map (unshift_by (num_new_rels - 1)) cs))
      sigma
  else
    diff_ind_case opts (diff opts) assums envs c_terms goals sigma

(*
 * Base case
 *)
let diff_base_case opts =
  break_diff_ind_case (set_is_ind opts false)

(*
 * Inductive case
 *)
let diff_inductive_case opts =
  let change = get_change opts in
  let opts = if is_identity change then opts else set_is_ind opts true in
  break_diff_ind_case opts

(*
 * Depending on whether a proof has inductive hypotheses, difference
 * it treating it either like a base case (no inductive hypotheses)
 * or an inductive case (some inductive hypotheses).
 *)
let diff_base_or_inductive_case num_ihs =
  if num_ihs > 0 then
    diff_inductive_case
  else
    diff_base_case

(*
 * Diff a case, then adjust the patch so it type-checks
 * in the original envionment.
 *
 * If there is a bug here, then the offset we unshift by may not generalize
 * for all cases.
 *
 * TODO wrap/cleanup args (when using lambdas, will be nicer hopefully)
 *)
let diff_and_unshift_case num_ihs opts diff assums envs_old goals_old envs goals c_envs c_terms c_goals =
  bind
    (diff_base_or_inductive_case num_ihs opts diff assums envs_old goals_old envs goals c_envs c_terms c_goals)
    (map_state
       (fun trm ->
         if is_conclusion (get_change opts) then
           ret (unshift_by (List.length (fst c_terms) + num_ihs) trm)
         else
           ret trm))

(*
 * Search in a diff that has been broken up into different cases.
 * That is, search the base case, inductive case, and so on separately.
 *
 * For now, we only return the first patch we find.
 * We may want to return more later.
 *
 * TODO clean up args at some point
 *)
let rec diff_ind_cases opts diff assums envs_old goals_old cases_data sigma =
  match cases_data with
  | (envs, goals, c_envs, c_terms, c_goals, num_ihs) :: tl ->
     bind
       (diff_and_unshift_case num_ihs opts diff assums envs_old goals_old envs goals c_envs c_terms c_goals)
       (fun patches sigma_h ->
         if non_empty patches then
           ret patches sigma_h
         else
           diff_ind_cases opts diff assums envs_old goals_old tl sigma)
       sigma
  | [] ->
     ret [] sigma

(* --- Top-level --- *)

(*
 * Search an inductive proof for a patch.
 * That is, break it into cases, and search those cases for patches.
 *
 * This does not yet handle nested inducted proofs.
 *
 * This does not yet handle the case when the inductive parameters
 * are lists of different lengths, or where there is a change in hypothesis.
 *)
let diff_inductive diff envs_old goals_old opts assums envs elims goals sigma =
  let elim_o, elim_n = elims in
  let nparams_o, nparams_n = map_tuple List.length (elim_o.pms, elim_n.pms) in
  if not (nparams_o = nparams_n) then
    ret give_up sigma
  else
    let sigma, (os, ns, assums) = eval_induction_cat assums envs elims sigma in
    let cases_data =
      List.map
        (fun (o, n) ->
          let (o_t, n_t) = map_tuple terminal (o, n) in
          let envs = map_tuple context_env (o_t, n_t) in
          let goals = map_tuple context_term (o_t, n_t) in
          let ms = map_tuple morphisms (o, n) in
          let (ms_o, ms_n) =
            map_tuple (List.filter (fun (_, e, _) -> not (ext_is_ih e))) ms
          in
          let c_dsts = map_tuple conclusions (map_tuple all_but_last (ms_o, ms_n)) in
          let c_envs = map_tuple (List.map context_env) c_dsts in
          let c_goals = map_tuple (List.map context_term) c_dsts in
          let c_terms =
            map_tuple (fun ms -> List.rev (List.map (fun (_, e, _) -> ext_term e) ms)) (ms_o, ms_n)
          in
          let num_ihs = List.length (fst ms) - List.length ms_o in
          (envs, goals, c_envs, c_terms, c_goals, num_ihs))
        (List.combine os ns)
    in
    bind
      (diff_ind_cases opts diff assums envs_old goals_old cases_data)
      (map_state (fun d -> ret (unshift_by nparams_o d)))
      sigma
