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
let merge_diff_envs is_ind num_new_rels (d : goal_type_term_diff) =
  let (_, _, assums) = d in
  let (env, ns, os) = merge_diff_closures d [] in
  let [new_goal_type; new_term] = ns in
  let [old_goal_type; old_term] = os in
  bind
    (sub_new_ih is_ind num_new_rels env old_term)
    (fun old_term_sub ->
      let n = (new_goal_type, new_term) in
      let o = (old_goal_type, old_term_sub) in
      ret (env, (o, n, assums)))

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
let build_app_candidates_no_red env opts from_type old_term new_term =
  try
    let env_b = push_local (Name.Anonymous, from_type) env in
    let old_term_shift = shift old_term in
    bind
      (if is_identity (get_change opts) then
	(* the difference between a term and nothing is the term *)
	ret [old_term_shift]
      else
        (* otherwise, check containment *)
	let new_term_shift = shift new_term in
        bind
          (fun sigma ->
            let sub = (new_term_shift, mkRel 1) in
            all_conv_substs_combs env_b sigma sub old_term_shift)
          (fun subbed sigma ->
            filter_not_same old_term_shift env_b sigma subbed))
      (map_state (fun b -> ret (reconstruct_lambda_n env_b b (nb_rel env))))
  with _ ->
    ret give_up

(*
 * Build app candidates, then remove identity functions
 *)
let build_app_candidates env opts from_type old_term new_term =
  bind
    (build_app_candidates_no_red env opts from_type old_term new_term)
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
 *)
let find_difference (opts : options) (d : goal_proof_diff) =
  let d = proof_to_term d in
  let d = swap_search_goals opts d in
  let d_dest = dest_goals d in
  let num_new_rels = num_new_bindings (fun o -> snd (fst o)) d_dest in
  let is_ind = is_ind opts in
  bind
    (merge_diff_envs is_ind num_new_rels d_dest)
    (fun (env, d) ->
      let ((old_goal_type, old_term), (new_goal_type, new_term), _) = d in
      let goal_type = mkProd (Name.Anonymous, new_goal_type, shift old_goal_type) in
      let change = get_change opts in
      bind
        (if is_hypothesis change then
           ret new_goal_type
         else
           fun sigma -> infer_type env sigma new_term)
        (fun from_type ->
          bind
            (build_app_candidates env opts from_type old_term new_term)
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
let no_diff opts (d : goal_proof_diff) =
  let change = get_change opts in
  if is_identity change then
    (* there is always a difference between the term and nothing *)
    ret false
  else
    (* check convertibility *)
    let d_term = proof_to_term d in
    let d_dest = dest_goals d_term in
    let num_new_rels = num_new_bindings (fun o -> snd (fst o)) d_dest in
    bind
      (merge_diff_envs false num_new_rels d_dest)
      (fun (env, d_merge) ->
        let ((_, old_term), (_, new_term), _) = d_merge in
        bind
          (fun sigma -> convertible env sigma old_term new_term)
          (fun conv ->
            match change with
            | FixpointCase ((d_old, d_new), _) ->
               ret (conv
                    || (equal d_old old_term && equal d_new new_term)
                    || (equal d_old new_term && equal d_new old_term))
            | _ ->
               ret conv))

(*
 * Given a difference in proofs with contexts storing the goals,
 * return the singleton list with the polymorphic identity function
 * applied to the type of the goal.
 *
 * TODO: This is incorrect in some cases:
 * Inside of lambdas, we need to adjust this.
 *)
let identity_candidates ((_, _), (new_goal, _), _) =
  bind
    (fun sigma ->
      identity_term (context_env new_goal) sigma (context_term new_goal))
    (fun t -> ret [t])
