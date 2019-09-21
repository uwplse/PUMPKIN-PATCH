(* --- Differencing of Proofs --- *)

open Proofcatterms
open Constr
open Environ
open Searchopts
open Substitution
open Proofdiff
open Debruijn
open Evd
open Filters
open Candidates
open Reducers
open Kindofchange
open Names
open Zooming
open Contextutils
open Idutils
open Stateutils
open Convertibility
open Envutils
open Inference
open Utilities
open Merging
open Assumptions

(* --- Utilities --- *)

(*
 * Given a term for the old proof, in the inductive case, substitute in
 * the IH from the new case for every term
 * whose type is convertible to the type of the IH from the new case.
 * In the base case, or outside of inductive proofs, do nothing.
 *
 * In other words, if the IH : (n > 0) for a proof over the nats,
 * then this will substitute every term of type (n > 0) inside of the old
 * proof with IH. We can then more easily relate the new and old
 * proof terms when we try to abstract the candidates to work
 * outside of the inductive case.
 *
 * This may capture more terms than we want, and so is a heuristic.
 * Eventually we might want to improve this. Possible problems here
 * are similar to the problems we encounter in general when
 * abstracting candidates.
 *)
let sub_new_ih is_ind num_new_rels env (old_term : types) sigma =
  if is_ind then
    let ih_new = mkRel (1 + num_new_rels) in
    all_typ_substs env sigma (ih_new, ih_new) old_term
  else
    sigma, old_term

(*
 * Merge the environments in a diff and factor out the enviroment
 * Subtitute in the inductive hypothesis if in the inductive case
 *)
let merge_diff_envs assums is_ind num_new_rels envs (trm_o, trm_n) (typ_o, typ_n) =
  let (env, [typ_o; trm_o], [typ_n; trm_n]) =
    merge_term_lists envs ([typ_o; trm_o], [typ_n; trm_n]) assums
  in
  bind
    (sub_new_ih is_ind num_new_rels env trm_o)
    (fun trm_o -> ret (env, (trm_o, trm_n), (typ_o, typ_n)))

(* --- Differencing of Proofs --- *)

(*
 * Try to identify the new proof term inside of the old proof term
 * and then factor it out.
 *
 * Specifically, given two proof terms:
 * old_term = t1 t2 : T_old
 * new_term = t : T_new
 *
 * Build candidates for a direct patch as follows:
 * 1. Push some (H : T_new) into the common environment (and adjust indexes)
 * 2. Look for all subterms of (t1 t2) that are convertible to t
 * 3. Substitute all combinations of those subterms with H
 * 4. Remove the original term from the list
 * 5. Wrap those in a lambda from (H : T_new)
 * 6. Return the list of candidates (don't check that they are patches yet)
 *
 * For optimization, we just return the original term.
 *)
let build_app_candidates_no_red env opts from_type (trm_o, trm_n) =
  try
    let num_rels = nb_rel env in
    let env = push_local (Name.Anonymous, from_type) env in
    let trm_o = shift trm_o in
    bind
      (if is_identity (get_change opts) then
	(* the difference between a term and nothing is the term *)
	ret [trm_o]
      else
        (* otherwise, check containment *)
	let trm_n = shift trm_n in
        bind
          (fun sigma ->
            let sub = (trm_n, mkRel 1) in
            all_conv_substs_combs env sigma sub trm_o)
          (fun subbed sigma ->
            filter_not_same trm_o env sigma subbed))
      (map_state (fun b -> ret (reconstruct_lambda_n env b num_rels)))
  with _ ->
    ret give_up

(*
 * Build app candidates, then remove identity functions
 *)
let build_app_candidates env opts from_type trms =
  bind
    (build_app_candidates_no_red env opts from_type trms)
    (fun cs sigma -> reduce_all reduce_remove_identities env sigma cs)

(*
 * Given two proof terms that apply functions, old and new,
 * try to find a patch that goes from the conclusion of new
 * back to the conclusion of old.
 *
 * This is the primitive differencing function.
 *
 * The is_ind boolean determines when we are in the inductive
 * case of an inductive proof and have just encountered two different
 * inductive hypotheses. In that case, we do some extra substitution
 * to make the inductive hypothesis of the new proof explicit
 * in the old proof, then reduce to try to eliminate the
 * old inductive hypothesis. This is the only heuristic implemented
 * so far that handles direct patches showing up in inductive cases,
 * since otherwise the type will not be correct. There is a benchmark
 * for this. Nonetheless, we should improve it when we try other
 * proofs that exercise this case.
 *
 * It's unclear whether this is useful for simple non-inductive proofs
 * with application. We should make a benchmark for this,
 * and then try calling this from the top-level search procedure.
 * In theory, it should work.
 *
 * Currently heuristics-driven, and does not work for all cases.
 *
 * TODO refactor out some of the goal making an env merging logic, once we
 * fix the other differencers, before merging
 *)
let find_difference (opts : options) assums envs terms goals =
  let terms = swap_search_proofs opts terms in
  let num_new_rels = num_assumptions (complement_assumptions assums (fst envs)) in
  let is_ind = is_ind opts in
  bind
    (merge_diff_envs assums is_ind num_new_rels envs terms goals)
    (fun (env, terms, goals) ->
      let (goal_o, goal_n) = goals in
      let goal_type = mkProd (Name.Anonymous, goal_n, shift goal_o) in
      let change = get_change opts in
      bind
        (if is_hypothesis change then
           ret goal_n
         else
           let (_, term_n) = terms in
           fun sigma -> infer_type env sigma term_n)
        (fun from_type ->
          bind
            (build_app_candidates env opts from_type terms)
            (fun cs ->
              let unshift_c = unshift_local (num_new_rels - 1) num_new_rels in
              let filter_gt l sigma = filter_by_type goal_type env sigma l in
              let filter l =
                bind
                  (branch_state
                     (fun _ -> ret is_ind)
                     (fun l sigma -> filter_ihs env sigma l)
                     ret
                     l)
                  filter_gt
              in bind (filter cs) (fun l -> ret (List.map unshift_c l)))))
        
(* Determine if two diffs are identical (convertible). *)
let no_diff opts assums envs terms goals =
  let change = get_change opts in
  if is_identity change then
    (* there is always a difference between the term and nothing *)
    ret false
  else
    (* check convertibility *)
    let num_new_rels = num_assumptions (complement_assumptions assums (fst envs)) in
    bind
      (merge_diff_envs assums false num_new_rels envs terms goals)
      (fun (env, (term_o, term_n), _) ->
        bind
          (fun sigma -> convertible env sigma term_o term_n)
          (fun conv ->
            match change with
            | FixpointCase ((d_old, d_new), _) ->
               ret (conv
                    || (equal d_old term_o && equal d_new term_n)
                    || (equal d_old term_n && equal d_new term_o))
            | _ ->
               ret conv))

(*
 * Given a difference in proofs with contexts storing the goals,
 * return the singleton list with the polymorphic identity function
 * applied to the type of the goal.
 *
 * TODO: This is incorrect in some cases:
 * Inside of lambdas, we need to adjust this.
 *
 * TODO left off here
 *)
let identity_candidates ((_, _), (new_goal, _), _) =
  bind
    (fun sigma ->
      identity_term (context_env new_goal) sigma (context_term new_goal))
    (fun t -> ret [t])
