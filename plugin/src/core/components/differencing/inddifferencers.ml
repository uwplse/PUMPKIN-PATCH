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
  | ((term_o :: tl_o), (term_n :: tl_n)) -> (* TODO move to HOF? *)
     try_chain_diffs
       [(fun assums envs terms goals sigma -> (* TODO move to HOF try_diff? *)
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
let diff_ind_case opts diff d sigma =
  let ((goal1, os), (goal2, ns), assums) = d in
  let envs = map_tuple context_env (goal1, goal2) in
  let goals = map_tuple context_term (goal1, goal2) in
  let sigma, (os, ns) = map_tuple_state (filter_state (fun (_, e, _) -> ret (not (ext_is_ih e)))) (os, ns) sigma in
  let sigma, (os, ns) = map_tuple_state (map_state eval_proof_arrow) (os, ns) sigma in
  let (os, ns) = map_tuple (List.map only_extension_as_term) (os, ns) in
  diff_case (abstract_case opts d) diff assums envs (os, ns) goals sigma

(*
 * Search a case of a difference in proof categories.
 * Return a patch if we find one.
 *
 * This breaks it up into arrows and then searches those
 * in the order of the sort function.
 *)
let diff_sort_ind_case opts sort diff envs_old terms_old goals_old (o, n, assums) =
  let ms_o = morphisms o in
  let ms_n = morphisms n in
  let d_ms = ms_o, ms_n, assums in
  bind
    (bind
      (map_diffs
         (fun (o, ms) -> ret (terminal o, ms))
         (fun _ -> update_case_assums d_ms)
         ((o, sort o ms_o), (n, sort n ms_n), assums))
      (fun ds -> ret (reset_case_goals opts envs_old terms_old goals_old ds)))
    (fun d_goals ->
      if is_hypothesis (get_change opts) then
        (* deal with the extra hypothesis *)
        let ((goal_o_o, _), (_, _), _) = d_goals in
        let env_o_n = fst envs_old in
        let env_o_o = context_env goal_o_o in
        let num_new_rels = new_rels2 env_o_o env_o_n in
        bind
          (diff_ind_case opts (diff opts) d_goals)
          (fun ds -> ret (List.map (unshift_by (num_new_rels - 1)) ds))
      else
        diff_ind_case opts (diff opts) d_goals)

(*
 * Base case: Prefer arrows later in the proof
 *)
let diff_base_case opts diff envs_old terms_old goals_old d =
  let sort _ ms = List.rev ms in
  diff_sort_ind_case (set_is_ind opts false) sort diff envs_old terms_old goals_old d

(*
 * Inductive case: Prefer arrows closest to an IH,
 * and in a tie, prefer arrows that are later.
 *
 * There currently may not be a guarantee that the two
 * arrows are traversed in exactly the same order for each proof.
 * If there is a bug in this, this may be why.
 *
 * For optimization, we don't bother treating the inductive case
 * any differently, since the IH does not change.
 *)
let diff_inductive_case opts diff envs_old terms_old goals_old d sigma =
  let sort c ms =
    (* Porting stable_sort to state is just not happening *)
    List.stable_sort
      (fun m1 m2 -> snd (closer_to_ih c (find_ihs c) m1 m2 sigma))
      ms
  in
  let change = get_change opts in
  let opts = if is_identity change then opts else set_is_ind opts true in
  diff_sort_ind_case opts sort diff envs_old terms_old goals_old d sigma

(*
 * Depending on whether a proof has inductive hypotheses, difference
 * it treating it either like a base case (no inductive hypotheses)
 * or an inductive case (some inductive hypotheses).
 *)
let diff_base_or_inductive_case opts diff envs_old terms_old goals_old d =
  let (o, _, _) = d in
  if has_ihs o then
    diff_inductive_case opts diff envs_old terms_old goals_old d
  else
    diff_base_case opts diff envs_old terms_old goals_old d

(*
 * Diff a case, then adjust the patch so it type-checks
 * in the original envionment.
 *
 * If there is a bug here, then the offset we unshift by may not generalize
 * for all cases.
 *)
let diff_and_unshift_case opts diff envs_old terms_old goals_old d =
  let (o, _, _) = d in
  bind
    (diff_base_or_inductive_case opts diff envs_old terms_old goals_old d)
    (map_state
       (fun trm ->
         if is_conclusion (get_change opts) then
           ret (unshift_by (List.length (morphisms o)) trm)
         else
           ret trm))

(*
 * Search in a diff that has been broken up into different cases.
 * That is, search the base case, inductive case, and so on separately.
 *
 * For now, we only return the first patch we find.
 * We may want to return more later.
 *)
let rec diff_ind_cases opts diff envs_old terms_old goals_old ds sigma =
  match ds with
  | d :: tl ->
     bind
       (diff_and_unshift_case opts diff envs_old terms_old goals_old d)
       (fun patches sigma_h ->
         if non_empty patches then
           ret patches sigma_h
         else
           diff_ind_cases opts diff envs_old terms_old goals_old tl sigma)
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
let diff_inductive diff envs_old terms_old goals_old opts assums envs elims goals sigma =
  let elim_o, elim_n = elims in
  let nparams_o, nparams_n = map_tuple List.length (elim_o.pms, elim_n.pms) in
  if not (nparams_o = nparams_n) then
    ret give_up sigma
  else
    let sigma, (os, ns, assums) = eval_induction_cat assums envs elims sigma in
    let ds = List.map2 (fun o n -> o, n, assums) os ns in
    bind
      (diff_ind_cases opts diff envs_old terms_old goals_old ds)
      (map_state (fun d -> ret (unshift_by nparams_o d)))
      sigma
