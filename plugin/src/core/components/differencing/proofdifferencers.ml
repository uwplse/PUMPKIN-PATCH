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
open Convertibility
open Contextutils
open Idutils

(* --- TODO for refactoring without breaking things --- *)

(*
 * Infer the type of trm in env
 * Note: This does not yet use good evar map hygeine; will fix that
 * during the refactor.
 *)
let infer_type (env : env) (evd : evar_map) (trm : types) : types =
  let jmt = Typeops.infer env trm in
  j_type jmt
               
(* --- End TODO --- *)

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
let sub_new_ih is_ind num_new_rels env evd (old_term : types) : types =
  if is_ind then
    let ih_new = mkRel (1 + num_new_rels) in
    all_typ_substs env evd (ih_new, ih_new) old_term
  else
    old_term

(*
 * Merge the environments in a diff and factor out the enviroment
 * Subtitute in the inductive hypothesis if in the inductive case
 *)
let merge_diff_envs is_ind num_new_rels evd (d : goal_type_term_diff)  =
  let assums = assumptions d in
  let (env, ns, os) = merge_diff_closures d [] in
  let [new_goal_type; new_term] = ns in
  let [old_goal_type; old_term] = os in
  let old_term_sub = sub_new_ih is_ind num_new_rels env evd old_term in
  let n = (new_goal_type, new_term) in
  let o = (old_goal_type, old_term_sub) in
  (env, difference o n assums)

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
let build_app_candidates env evd opts (from_type : types) (old_term : types) (new_term : types) =
  try
    let env_b = push_rel CRD.(LocalAssum(Name.Anonymous, from_type)) env in
    let old_term_shift = shift old_term in
    let bodies =
      if is_identity (get_change opts) then
	(* the difference between a term and nothing is the term *)
	[old_term_shift]
      else
        (* otherwise, check containment *)
	let new_term_shift = shift new_term in
	let sub = all_conv_substs_combs env_b evd (new_term_shift, (mkRel 1)) in
	filter_not_same old_term_shift env_b evd (sub old_term_shift)
    in List.map (fun b -> reconstruct_lambda_n env_b b (nb_rel env)) bodies
  with _ ->
    give_up

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
let find_difference evd (opts : options) (d : goal_proof_diff) : candidates =
  let d = proof_to_term d in
  let d = swap_search_goals opts d in
  let d_dest = dest_goals d in
  let num_new_rels = num_new_bindings (fun o -> snd (fst o)) d_dest in
  let is_ind = is_ind opts in
  let (env_merge, d_merge) = merge_diff_envs is_ind num_new_rels evd d_dest in
  let (old_goal_type, old_term) = old_proof d_merge in
  let (new_goal_type, new_term) = new_proof d_merge in
  let change = get_change opts in
  let from_type =
    if is_hypothesis change then
      new_goal_type
    else
      infer_type env_merge evd new_term
  in
  let candidates = build_app_candidates env_merge evd opts from_type old_term new_term in
  let goal_type = mkProd (Name.Anonymous, new_goal_type, shift old_goal_type) in
  let reduced = reduce_all reduce_remove_identities env_merge evd candidates in
  let filter = filter_by_type goal_type env_merge evd in
  List.map
    (unshift_local (num_new_rels - 1) num_new_rels)
    (filter (if is_ind then filter_ihs env_merge evd reduced else reduced))

(* Determine if two diffs are identical (convertible). *)
let no_diff evd opts (d : goal_proof_diff) : bool =
  let change = get_change opts in
  if is_identity change then
    (* there is always a difference between the term and nothing *)
    false
  else
    (* check convertibility *)
    let d_term = proof_to_term d in
    let d_dest = dest_goals d_term in
    let num_new_rels = num_new_bindings (fun o -> snd (fst o)) d_dest in
    let (env, d_merge) = merge_diff_envs false num_new_rels evd d_dest in
    let (_, old_term) = old_proof d_merge in
    let (_, new_term) = new_proof d_merge in
    let conv = convertible env evd old_term new_term in
    match change with
    | FixpointCase ((d_old, d_new), _) ->
       conv
       || (equal d_old old_term && equal d_new new_term)
       || (equal d_old new_term && equal d_new old_term)
    | _ ->
       conv

(*
 * Given a difference in proofs with contexts storing the goals,
 * return the singleton list with the polymorphic identity function
 * applied to the type of the goal.
 *
 * TODO: This is incorrect in some cases:
 * Inside of lambdas, we need to adjust this.
 *
 * TODO better evar_map hygiene
 *)
let identity_candidates (d : goal_proof_diff) : candidates =
  let (new_goal, _) = new_proof d in
  let env = context_env new_goal in
  let sigma = Evd.from_env env in
  [snd (identity_term (context_env new_goal) sigma (context_term new_goal))]
