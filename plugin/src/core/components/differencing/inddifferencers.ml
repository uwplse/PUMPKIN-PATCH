(* --- Differencing of Inductive Proofs --- *)

open Utilities
open Collections
open Proofcat
open Proofcatterms
open Proofdiff
open Candidates
open Evaluation
open Zooming
open Debruijn
open Kindofchange
open Searchopts
open Abstraction
open Expansion
open Environ

(* --- Cases --- *)

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
let diff_sort_ind_case opts sort diff d_old (d : proof_cat_diff) : candidates =
  let o = old_proof d in
  let n = new_proof d in
  let ms_o = morphisms o in
  let ms_n = morphisms n in
  let d_ms = difference ms_o ms_n (assumptions d) in
  let d_goals =
    reset_case_goals
      opts
      d_old
      (map_diffs
         (fun (o, ms) -> (terminal o, ms))
         (always (update_case_assums d_ms))
         (add_to_diff d (sort o ms_o) (sort n ms_n)))
  in
  if is_hypothesis (get_change opts) then
    (* deal with the extra hypothesis *)
    let env_o_o = context_env (fst (old_proof d_goals)) in
    let env_o_n = context_env (fst (old_proof d_old)) in
    let num_new_rels = nb_rel env_o_o - nb_rel env_o_n in
    List.map
      (unshift_by (num_new_rels - 1))
      (diff_ind_case opts (diff opts) d_goals)
  else
    diff_ind_case opts (diff opts) d_goals


(*
 * Base case: Prefer arrows later in the proof
 *)
let diff_base_case opts diff d_old (d : proof_cat_diff) : candidates =
  let sort _ ms = List.rev ms in
  diff_sort_ind_case (set_is_ind opts false) sort diff d_old d

(*
 * Inductive case: Prefer arrows closest to an IH,
 * and in a tie, prefer arrows that are later.
 *
 * There currently may not be a guarantee that the two
 * arrows are traversed in exactly the same order for each proof.
 * If there is a bug in this, this may be why.
 *)
let diff_inductive_case opts diff d_old (d : proof_cat_diff) : candidates =
  let sort c ms = List.stable_sort (closer_to_ih c (find_ihs c)) ms in
  diff_sort_ind_case (set_is_ind opts true) sort diff d_old d

(*
 * Depending on whether a proof has inductive hypotheses, difference
 * it treating it either like a base case (no inductive hypotheses)
 * or an inductive case (some inductive hypotheses).
 *)
let diff_base_or_inductive_case opts diff d_old (d : proof_cat_diff) : candidates =
  let o = old_proof d in
  if has_ihs o then
    diff_inductive_case opts diff d_old d
  else
    diff_base_case opts diff d_old d

(*
 * Diff a case, then adjust the patch so it type-checks
 * in the original envionment.
 *
 * If there is a bug here, then the offset we unshift by may not generalize
 * for all cases.
 *)
let diff_and_unshift_case opts diff d_old (d : proof_cat_diff) : candidates =
  List.map
    (fun trm ->
      if is_conclusion (get_change opts) then
        unshift_by (List.length (morphisms (old_proof d))) trm
      else
        trm)
    (diff_base_or_inductive_case opts diff d_old d)

(*
 * Search in a diff that has been broken up into different cases.
 * That is, search the base case, inductive case, and so on separately.
 *
 * For now, we only return the first patch we find.
 * We may want to return more later.
 *)
let rec diff_ind_cases opts diff d_old (ds : proof_cat_diff list) : candidates =
  match ds with
  | d :: tl ->
     let patches = diff_and_unshift_case opts diff d_old d in
     if non_empty patches then
       patches
     else
       diff_ind_cases opts diff d_old tl
  | [] ->
     []

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
let diff_inductive diff d_old opts (d : (proof_cat * int) proof_diff) : candidates =
  let (o, nparams_o) = old_proof d in
  let (n, nparams_n) = new_proof d in
  if not (nparams_o = nparams_n) then
    give_up
  else
    zoom_map
      (fun d ->
        let sort c = base_cases_first (List.map expand_constr (split c)) in
        let d_sorted = map_diffs sort id d in
        let ds = dest_cases d_sorted in
        List.map (unshift_by nparams_o) (diff_ind_cases opts diff d_old ds))
      []
      id
      (intro_params nparams_o)
      (difference o n (assumptions d))
