(* --- Differencing Component --- *)

open Proofcat
open Proofcatterms
open Searchopts
open Proofdiff
open Assumptions
open Term
open Substitution
open Environ
open Coqterms
open Debruijn
open Filters
open Reducers
open Candidates
open Collections
open Coqenvs
open Cutlemma
open Kindofchange
open Printing
open Specialization

type ('a, 'b) differencer = 'a proof_diff -> 'b

type 'a candidate_differencer = ('a, candidates) differencer
type proof_differencer = (context_object * proof_cat) candidate_differencer
type term_differencer = types candidate_differencer
type args_differencer = (types array) candidate_differencer

type 'a change_detector = ('a, kind_of_change) differencer
type proof_change_detector = (context_object * proof_cat) change_detector

type 'a predicate_differencer = ('a, bool) differencer
type proof_diff_predicate = (context_object * proof_cat) predicate_differencer

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
let sub_new_ih is_ind num_new_rels env (old_term : types) : types =
  if is_ind then
    let ih_new = mkRel (1 + num_new_rels) in
    all_typ_substs env (ih_new, ih_new) old_term
  else
    old_term

(*
 * Merge the environments in a diff and factor out the enviroment
 * Subtitute in the inductive hypothesis if in the inductive case
 *)
let merge_diff_envs is_ind num_new_rels (d : goal_type_term_diff)  =
  let assums = assumptions d in
  let (env, ns, os) = merge_diff_closures d [] in
  let [new_goal_type; new_term] = ns in
  let [old_goal_type; old_term] = os in
  let old_term_sub = sub_new_ih is_ind num_new_rels env old_term in
  let n = (new_goal_type, new_term) in
  let o = (old_goal_type, old_term_sub) in
  (env, difference o n assums)

(* --- Determining what has changed --- *)

(*
 * If the kind of change is a change in conclusion, then
 * determine whether the first different term is a constructor or
 * an induction principle.
 *
 * This is a heuristic and may sometimes be wrong, so we should
 * expose an option to users as well (TODO).
 *)
let find_kind_of_conclusion cut (d : goal_proof_diff) =
  let (trm_o, trm_n) = proof_terms d in
  let rec configure trm_o trm_n =
    match kinds_of_terms (trm_o, trm_n) with
    | (Lambda (_, _, b_o), _) ->
       configure b_o trm_n
    | (_, Lambda (_, _, b_n)) ->
       configure trm_o b_n
    | (App (f_o, _), App (f_n, _)) when isConstruct f_o && isConstruct f_n ->
       ConclusionCase cut
    | _ ->
       Conclusion
  in configure trm_o trm_n

(*
 * Determine the kind of change to search for (type differencing for proofs).
 * Search for a difference in type only if the type is a product
 * that takes a non-convertible premise, and that premise is a different
 * inductive type with the same shape.
 *
 * Otherwise, if the new conclusion contains some constant function that has
 * changed from a constant function in the same place in the old conclusion,
 * but all of its arguments are the same, then search for a difference in
 * definitions.
 *
 * Otherwise, search for a change in conclusion.
 *)
let find_kind_of_change (cut : cut_lemma option) (d : goal_proof_diff) =
  let d_goals = erase_proofs d in
  let goals = goal_types d_goals in
  let env = context_env (old_proof d_goals) in
  let r = reduce_remove_identities env in
  let old_goal = r (fst goals) in
  let new_goal = r (snd goals) in
  let rec diff env typ_o typ_n =
    match kinds_of_terms (typ_o, typ_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if (not (convertible env t_o t_n)) then
         let change = InductiveType (t_o, t_n) in
         let d_typs = difference t_o t_n no_assumptions in
         if same_shape env d_typs then
           InductiveType (t_o, t_n)
         else
           Conclusion
       else
         diff (push_rel (n_o, None, t_o) env) b_o b_n
    | (App (f_o, args_o), App (f_n, args_n)) ->
       if (not (same_length args_o args_n)) then
         Conclusion
       else
         if isConst f_o && isConst f_n && (not (convertible env f_o f_n)) then
           if args_convertible env args_o args_n then
             if not (Option.has_some cut) then
               failwith "Must supply cut lemma for change in fixpoint"
             else
               FixpointCase ((f_o, f_n), Option.get cut)
           else
             Conclusion
         else
           let conf_args = apply_to_arrays (List.map2 (diff env)) in
           let arg_confs = conf_args args_o args_n in
           if List.for_all is_conclusion arg_confs then
             Conclusion
           else
             List.find (fun change -> not (is_conclusion change)) arg_confs
    | _ ->
       Conclusion
  in
  let change = diff env old_goal new_goal in
  if is_conclusion change then
    find_kind_of_conclusion cut d
  else
    change

(* --- Differencing of proofs --- *)

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
 * 4. Filter out the original term, which isn't substituted at all
 * 5. Wrap those in a lambda from (H : T_new)
 * 6. Return the list of candidates (don't check that they are patches yet)
 *)
let build_app_candidates (env : env) (old_term : types) (new_term : types) =
  try
    let new_type = infer_type env new_term in
    let env_shift = push_rel (Anonymous, None, new_type) env in
    let old_term_shift = shift old_term in
    let new_term_shift = shift new_term in
    let sub = all_conv_substs_combs env_shift (new_term_shift, (mkRel 1)) in
    let bodies = sub old_term_shift in
    List.map
      (fun b -> mkLambda (Anonymous, new_type, b))
      (filter_not_same env_shift old_term_shift bodies)
  with _ -> give_up

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
let find_difference (opts : options) (d : goal_proof_diff) : candidates =
  let d = proof_to_term d in
  let d = swap_search_goals opts d in
  let d_dest = dest_goals d in
  let num_new_rels = num_new_bindings (fun o -> snd (fst o)) d_dest in
  let (_, old_env) = fst (old_proof d_dest) in
  let (_, new_env) = fst (new_proof d_dest) in
  let is_ind = is_ind opts in
  let (env_merge, d_merge) = merge_diff_envs is_ind num_new_rels d_dest in
  let (old_goal_type, old_term) = old_proof d_merge in
  let (new_goal_type, new_term) = new_proof d_merge in
  let candidates = build_app_candidates env_merge old_term new_term in
  let reduced = reduce_all reduce_remove_identities env_merge candidates in
  let goal_type = mkProd (Anonymous, new_goal_type, shift old_goal_type) in
  let filter = filter_by_type env_merge goal_type in
  List.map
    (unshift_local (num_new_rels - 1) num_new_rels)
    (filter (if is_ind then filter_ihs env_merge reduced else reduced))

(* Determine if two diffs are identical (convertible). *)
let no_diff opts (d : goal_proof_diff) : bool =
  let d_term = proof_to_term d in
  let d_dest = dest_goals d_term in
  let num_new_rels = num_new_bindings (fun o -> snd (fst o)) d_dest in
  let (env, d_merge) = merge_diff_envs false num_new_rels d_dest in
  let (_, old_term) = old_proof d_merge in
  let (_, new_term) = new_proof d_merge in
  let conv = convertible env old_term new_term in
  match get_change opts with
  | FixpointCase ((d_old, d_new), _) ->
     conv
     || (eq_constr d_old old_term && eq_constr d_new new_term)
     || (eq_constr d_old new_term && eq_constr d_new old_term)
  | _ ->
     conv

(*
 * Given a difference in proofs with contexts storing the goals,
 * return the singleton list with the polymorphic identity function
 * applied to the type of the goal.
 *
 * TODO: This is incorrect in some cases:
 * Inside of lambdas, we need to adjust this.
 *)
let identity_candidates (d : goal_proof_diff) : candidates =
  let (new_goal, _) = new_proof d in
  [identity_term (context_env new_goal) (context_term new_goal)]

(* --- Recursive differencing --- *)

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
 *)
let diff_args (diff : term_differencer) d_args =
  let assums = assumptions d_args in
  let diff_arg a_o a_n = diff (difference a_o a_n assums) in
  apply_to_arrays (flat_map2 diff_arg) (old_proof d_args) (new_proof d_args)

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
           filter_diff_cut (diff_args (diff_rec diff_arg opts)) d_args_rev
      | ConclusionCase cut when isConstruct f_o && isConstruct f_n ->
         let diff_arg o d = if no_diff o d then give_up else diff_arg o d in
         filter_diff
           (fun args ->
             if Option.has_some cut then
               let args_lambdas = List.map (reconstruct_lambda env) args in
               filter_applies_cut env (Option.get cut) args_lambdas
             else
               args)
           (diff_args (diff_rec diff_arg (set_change opts Conclusion)))
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
            diff_args get_goal_reduced (difference args1 args2 no_assumptions)
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
       let diff_bs = diff_args (get_goal_fix env_m) in
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
      let ds = diff_args (diff_fix_case env_fix) (difference dso dsn assums) in
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


