(* Search procedures *)

open Environ
open Term
open Coqterms
open Coqenvs
open Substitution
open Debruijn
open Proofcat
open Proofcatterms
open Assumptions
open Abstraction
open Filters
open Proofdiff
open Specialization
open Evaluation
open Expansion
open Printing
open Collections
open Utilities
open Hofs
open Inverting
open Searchopts
open Factoring

(* --- Debugging --- *)

(* Debug the search function *)
let debug_search (d : goal_proof_diff) : unit =
  let (t_o, t_n) = proof_terms d in
  let d = dest_goals d in
  let ((old_goal, env_o), _) = old_proof d in
  let ((new_goal, env_n), _) = new_proof d in
  debug_term env_o t_o "old";
  debug_term env_n t_n "new";
  debug_term env_o old_goal "old goal";
  debug_term env_n new_goal "new goal";
  print_separator ()

(* --- Auxiliary functions for candidates and diffs --- *)

(* When we don't know how to find a patch, just give up *)
let give_up : candidates =
  []

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

(* Merge the environments in a diff and factor out the enviroment *)
let merge_diff_envs is_ind num_new_rels (d : goal_type_term_diff)  =
  let assums = assumptions d in
  let (env, ns, os) = merge_diff_closures d [] in
  let [new_goal_type; new_term] = ns in
  let [old_goal_type; old_term] = os in
  let old_term_sub = sub_new_ih is_ind num_new_rels env old_term in
  let n = (new_goal_type, new_term) in
  let o = (old_goal_type, old_term_sub) in
  (env, difference o n assums)

let merge_lift_diff_envs (d : lift_goal_diff) (cs : candidates) =
  let d = dest_lift_goals d in
  let assums = assumptions d in
  let (env, ns, os) = merge_lift_diff_closures d cs in
  let new_goal_type = List.hd ns in
  let old_goal_type = List.hd os in
  (env, difference old_goal_type new_goal_type assums, List.tl os)

(* Get the number of bindings that are not common to both proofs in d *)
let num_new_bindings (f : 'a -> env) (d : 'a proof_diff) =
  let assums = assumptions d in
  num_assumptions (complement_assumptions assums (f (old_proof d)))

(* Keep the same assumptions, but update the goals and terms for a diff *)
let eval_with_terms_goals opts t_o t_n d =
  let update = update_search_goals opts d in
  update (erase_goals (eval_with_terms t_o t_n d))

(* --- Type differencing --- *)

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
let rec get_goal_fix (env : env) (old_term : types) (new_term : types) : types list =
  if eq_constr old_term new_term then
    give_up
  else
    match kinds_of_terms (old_term, new_term) with
    | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) when convertible env t1 t2 ->
       List.map
         (fun c -> mkProd (n1, t1, c))
         (get_goal_fix (push_rel (n1, None, t1) env) b1 b2)
    | _ ->
       let rec get_goal_reduced env old_term new_term =
         let r = reduce_using reduce_unfold_whd env in
         let red_old = r old_term in
         let red_new = r new_term in
         match kinds_of_terms (red_old, red_new) with
         | (App (f1, args1), App (f2, args2)) when eq_constr f1 f2 ->
            let args1 = Array.to_list args1 in
            let args2 = Array.to_list args2 in
            List.flatten (List.map2 (get_goal_reduced env) args1 args2)
         | _ when not (eq_constr red_old red_new) ->
            let r = reduce_using reduce_unfold env in
            [r (mkProd (Anonymous, old_term, shift new_term))]
         | _ ->
            give_up
       in get_goal_reduced env old_term new_term

(* Same as the above, but at the top-level for the fixpoint itself *)
let rec goals_for_fix (env : env) (old_term : types) (new_term : types) : types list =
  let conv = convertible env in
  match kinds_of_terms (old_term, new_term) with
  | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) when conv t1 t2 ->
     goals_for_fix (push_rel (n1, None, t1) env) b1 b2
  | (Case (_, ct1, m1, bs1), Case (_, ct2, m2, bs2)) when conv m1 m2  ->
     if Array.length bs1 = Array.length bs2 then
       let bs1 = Array.to_list bs1 in
       let bs2 = Array.to_list bs2 in
       let env_m = push_rel (Anonymous, None, m1) env in
       List.map
         unshift
         (List.append
            (List.flatten (List.map2 (get_goal_fix env_m) bs1 bs2))
            (List.flatten (List.map2 (get_goal_fix env_m) bs2 bs1)))
     else
       give_up
  | _ ->
     give_up

(* --- Interacting with abstraction --- *)

(*
 * The code below is all workaround code for DeBruijn bugs. Seriously.
 * I have some workarounds to make sure I'm being
 * consistent in how I'm calling abstraction. This is all really boring
 * stuff that shouldn't exist that I'll fix after the prototype.
 * I assume if you've ever written a compiler that has to deal
 * with DeBruijn indexes, you can empathize.
 *)

(*
 * Apply a dependent proposition at an index to the goal
 * Auxiliary function for function abstraction
 * Workaround
 *)
let rec apply_prop pi goal =
  match kind_of_term goal with
  | Prod (n, t, b) when isProd b ->
     mkProd (n, t, apply_prop (shift_i pi) b)
  | Prod (n, t, b) ->
     let p = mkRel pi in
     mkProd (n, mkApp (p, Array.make 1 t), mkApp (shift p, Array.make 1 b))

(*
 * Get goals for abstraction by a function
 * Very preliminary, and also a workaround
 *)
let get_lifting_goals p_typ (env : env) (o : types) (n : types) : types list =
  let old_term = unwrap_definition env o in
  let new_term = unwrap_definition env n in
  match kinds_of_terms (old_term, new_term) with
  | (Fix ((_, i), (nso, tso, dso)), Fix ((_, j), (_, tsn, dsn))) when i = j ->
    let all_convertible = List.for_all2 (convertible env) in
    if all_convertible (Array.to_list tso) (Array.to_list tsn) then
      let env_fix = push_rel_context (bindings_for_fix nso tso) env in
      let dso = Array.to_list dso in
      let dsn = Array.to_list dsn in
      let goals = List.flatten (List.map2 (goals_for_fix env_fix) dso dsn) in
      let lambdas = List.map (reconstruct_lambda env_fix) goals in
      let apps = List.map (fun t -> mkApp (t, Array.make 1 n)) lambdas in
      let red_goals = reduce_all reduce_term env apps in
      List.map
        (fun goal ->
          let pi = 0 in
          apply_prop pi (mkProd (Anonymous, p_typ, shift goal)))
        (unique eq_constr red_goals)
    else
      failwith "Cannot infer goals for generalizing change in definition"
  | _ ->
     failwith "Not fixpoints"

(*
 * Get the type of the function for abstraction
 * Also a workaround
 *)
let rec get_prop_type env typ =
  match kind_of_term typ with
  | Prod (n, t, b) ->
     get_prop_type (push_rel (n, None, t) env) b
  | App (f, args) ->
     infer_type env f
  | _ ->
     failwith "can't get type of prop"

(*
 * Get the arguments for abstraction by arguments
 * Also a workaround
 *)
let rec get_lifting_goal_args pi (app : types) : types =
  match kind_of_term app with
  | Lambda (n, t, b) ->
     mkProd (n, t, get_lifting_goal_args (pi + 1) b)
  | App (f, args) ->
     mkApp (mkRel pi, args)
  | _ ->
     failwith "Cannot infer goals for generalizing arguments"

(*
 * Abstract a term by a function
 * Only handles one argument since it's a debruijn hack wrt the cut lemma
 * The good version of this is in patcher.ml4 and this will go away one day
 *)
let rec generalize_term strategies (env : env) (c : types) (g : types) : types list =
  match (kind_of_term c, kind_of_term g) with
  | (Lambda (n, t, cb), Prod (_, tb, gb)) when isLambda cb && isProd gb ->
     generalize_term strategies (push_rel (n, None, t) env) cb gb
  | (Lambda (_, _, _), Prod (_, gt, _)) when isApp gt ->
     let ct = infer_type env c in
     let (_, _, ctb) = destProd ct in
     if isApp ctb then
       let (f_base, _) = destApp (unshift ctb) in
       let f_goal = f_base in
       let args = Array.to_list (snd (destApp gt)) in
       let cs = [c] in
       let is_concrete = true in
       let abstraction_config = {is_concrete; env; args; cs; f_base; f_goal; strategies} in
       abstract_with_strategies abstraction_config
     else
       failwith "Cannot infer property to generalize"
  | _ ->
     failwith "Goal is inconsistent with term to generalize"

(* Same as above, but for arguments *)
let rec generalize_term_args strategies (env : env) (c : types) (g : types) : types list =
  match (kind_of_term c, kind_of_term g) with
  | (Lambda (n, t, cb), Prod (_, tb, gb)) ->
     generalize_term_args strategies (push_rel (n, None, t) env) cb gb
  | (Lambda (_, _, _), App (lemma, args)) ->
     let ct = infer_type env g in
     let rec get_lemma_functions typ =
       match kind_of_term typ with
       | Prod (n, t, b) when isProd b ->
          let (f_base, f_goal) = get_lemma_functions b in
          (mkLambda (n, t, f_base), mkLambda (n, t, f_goal))
       | Prod (n, t, b) ->
          (t, b)
       | _ ->
          failwith "Could not infer arguments to generalize"
     in
     let (f_base, f_goal) = get_lemma_functions (infer_type env lemma) in
     let args = Array.to_list args in
     let cs = [c] in
     let is_concrete = false in
     let abstraction_config = {is_concrete; env; args; cs; f_base; f_goal; strategies} in
     abstract_with_strategies abstraction_config
  | _ ->
     failwith "Goal is inconsistent with term to generalize"

(* --- Searching with zooming --- *)

(*
 * Zoom in, search, and apply some function
 *)
let zoom_search search opts (d : goal_proof_diff) : candidates =
  let update_goals = update_search_goals opts d in
  zoom_map
    (fun d -> search opts (update_goals d))
    give_up
    expand_terminal
    intro_common
    (erase_goals d)

(*
 * Zoom in, search, and wrap the result in a lambda from binding (n : t)
 *)
let zoom_wrap_lambda search opts n t (d : goal_proof_diff) : candidates =
  zoom_search
    (fun opts d ->
      let ((_, env), _) = old_proof (dest_goals d) in
      List.map (fun c -> mkLambda (n, t, c)) (search opts d))
    opts
    d

(*
 * Zoom in, search, and wrap the result in a prod from binding (n : t)
 *)
let zoom_wrap_prod search opts n t (d : goal_proof_diff) : candidates =
  zoom_search
    (fun opts d ->
      List.map (fun c -> mkProd (n, t, c)) (search opts d))
    opts
    d

(*
 * Zoom in, search, and unshift the result
 *)
let zoom_unshift search opts (d : goal_proof_diff) : candidates =
  zoom_search
    (fun opts d ->
      List.map unshift (search opts d))
    opts
    d

(* --- Abstraction for search --- *)

(*
 * Try to abstract candidate patches given the goal types of the old proof
 * and the new proof. This assumes the candidate patches are specialized
 * (for example, with type P 0 for some P) and tries to abstract them (into P n).
 *
 * If the list of candidates are empty, then this returns the empty list.
 *
 * If the goal types are not both function applications, then they are not
 * specialized, so we have nothing to abstract, and we return the original list.
 *
 * If the goal types are both specialized, then we lift (see lifting.ml/i) to
 * try to abstract them.
 *)
let try_lift_candidates strategies (d : lift_goal_diff) (cfs : candidates) : candidates =
  let goals = goal_types d in
  let goals_are_apps = fold_tuple (fun t1 t2 -> isApp t1 && isApp t2) goals in
  if goals_are_apps && List.length cfs > 0 then
    let (env, d_type, cs) = merge_lift_diff_envs d cfs in
    let new_goal_type = new_proof d_type in
    let old_goal_type = old_proof d_type in
    let (f_base, args_n) = destApp new_goal_type in
    let (f_goal, args_o) = destApp old_goal_type in
    map_if
      (List.for_all2 (convertible env) (Array.to_list args_n))
      (fun args ->
        let is_concrete = true in
        let abstraction_config = {is_concrete; env; args; cs; f_base; f_goal; strategies} in
        let lcs = abstract_with_strategies abstraction_config in
        let num_new_rels = num_new_bindings snd (dest_lift_goals d) in
        List.map (unshift_local (num_new_rels - 1) num_new_rels) lcs)
      (always give_up)
      (Array.to_list args_o)
  else
    cfs

(* --- Identity --- *)

(*
 * Given a difference in proofs with contexts storing the goals,
 * return the singleton list with the polymorphic identity function
 * applied to the type of the goal.
 *
 * This is incorrect in some cases:
 * Inside of lambdas, we need to adjust this.
 *)
let identity_candidates (d : 'a goal_diff) : candidates =
  let (new_goal, _) = new_proof d in
  [identity_term (context_env new_goal) (context_term new_goal)]

(* Determine if two goal_proof_diffs are identical (convertible). *)
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

(* --- Application --- *)

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
let find_difference opts (d : goal_term_diff) : types list =
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

(* Using some search function, recursively search the arguments *)
let search_args search_arg args_o args_n : candidates =
  List.flatten
    (List.map2 search_arg (Array.to_list args_o) (Array.to_list args_n))

(*
 * Given a search function and a difference between terms,
 * if the terms are applications (f args) and (f' args'),
 * then recursively search the difference in functions and/or arguments.
 *
 * This function mostly exists to workaround types that aren't properly
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
 *)
let search_app search_f search_arg opts (d : goal_proof_diff) : candidates =
  let same_length o n = (Array.length o = Array.length n) in
  let (_, env) = fst (old_proof (dest_goals d)) in
  match kinds_of_terms (proof_terms d) with
  | (App (f_o, args_o), App (f_n, args_n)) when same_length args_o args_n ->
     (match get_change opts with
      | InductiveType (_, _) ->
         search_f opts (eval_with_terms_goals opts f_o f_n d)
      | FixpointCase ((_, _), cut) ->
         let f = search_f opts (eval_with_terms_goals opts f_o f_n d) in
         let f_cut = (filter_cut env cut) f in
         if List.length f_cut > 0 then
           f_cut
         else
           let args =
             search_args
               (fun a_o a_n ->
                 let d_a = eval_with_terms_goals opts a_n a_o (reverse d) in
                 search_arg opts d_a)
               args_o
               args_n
           in (filter_cut env cut) args
      | ConclusionCase cut when isConstruct f_o && isConstruct f_n ->
         let opts = set_change opts Conclusion in
         let args =
           search_args
             (fun a_o a_n ->
	       let d = eval_with_terms_goals opts a_o a_n d in
	       if no_diff opts d then
		 give_up
	       else
                 search_arg opts d)
	     args_o
             args_n
         in
         if Option.has_some cut then
           let args_lambdas = List.map (reconstruct_lambda env) args in
           filter_applies_cut env (Option.get cut) args_lambdas
         else
           args
      | Conclusion ->
         let all_conv = List.for_all2 (convertible env) in
         if all_conv (Array.to_list args_o) (Array.to_list args_n) then
           let specialize = specialize_using specialize_no_reduce env in
           let combine_app = combine_cartesian specialize in
	   let f = search_f opts (eval_with_terms_goals opts f_o f_n d) in
	   let args = List.map (fun a_o -> [a_o]) (Array.to_list args_o)
           in combine_app f (combine_cartesian_append (Array.of_list args))
         else
           give_up)
  | _ ->
     give_up

(*
 * After doing induction, search the difference in final arguments
 * That we, differencing can detect the final arguments to apply to
 *
 * Right now, this is limiting. It does actually let you apply
 * to different final arguments, (it will recursively search
 * the difference in those arguments), but it assumes that there is only
 * one argument the property applies to.
 *
 * So, for example, the conclusion of the nat induction principle is:
 *   forall (n : nat), P n
 *
 * This looks for that n once it finds the difference in P, so it
 * can tell specialization what to do. But it doesn't handle
 * induction principles where the conclusion is something like:
 *   forall t1 t2, P t1 t2
 *
 * The correct way to fix this when we make semantic differencing
 * better is to detect how many arguments the conclusion of the induction
 * principle takes, and only look that far. Because we want to specialize
 * by that argument, but we don't want to specialize by extra arguments
 * that show up afterward, like hypothesis. The example in the paper
 * in Section 3 is a case where you can see an extra argument we don't
 * want to specialize by.
 *)
let diff_final opts search_arg env_o env_n args_o args_n d =
  let final_arg_o = List.hd args_o in
  let final_arg_n = List.hd args_n in
  combine_cartesian_append
    (Array.of_list
       (List.map2
          (fun arg_o arg_n ->
            let a_o = eval_proof env_o arg_o in
            let a_n = eval_proof env_n arg_n in
            let d = add_goals (difference a_n a_o (assumptions d)) in
            let specialize = specialize_using specialize_no_reduce env_o in
            List.map
              (fun p -> specialize p (Array.make 1 arg_o))
              (search_arg opts d))
          ([final_arg_o])
          ([final_arg_n])))

(*
 * Search an application of an induction principle.
 * Basically, use the normal induction differencing function,
 * then specialize to any final arguments (the reduction step
 * happens later for now).
 *
 * For changes in constructors or fixpoint cases, don't specialize.
 *)
let search_app_ind search_ind search_arg opts d : candidates =
  let d_proofs = erase_goals d in
  let o = old_proof d_proofs in
  let n = new_proof d_proofs in
  let d_ind = difference (o, 0, []) (n, 0, []) (assumptions d) in
  let d_opt = zoom_same_hypos d_ind in
  if Option.has_some d_opt then
    let d_zoom = Option.get d_opt in
    let assums = assumptions d_zoom in
    let (o, npms_old, final_args_old) = old_proof d_zoom in
    let (n, npms_new, final_args_new) = new_proof d_zoom in
    let env_o = context_env (fst (old_proof d)) in
    let env_n = context_env (fst (new_proof d)) in
    let f = search_ind opts (difference (o, npms_old) (n, npms_new) assums) in
    match get_change opts with
    | InductiveType (_, _) ->
       f
    | FixpointCase ((_, _), _) ->
       f
    | _ ->
       if List.length final_args_old > 0 then
         let args_o = final_args_old in
         let args_n = final_args_new in
         let args = diff_final opts search_arg env_o env_n args_o args_n d in
         let specialize = specialize_using specialize_no_reduce env_o in
         combine_cartesian specialize f args
       else
         f
  else
    give_up

(* Given a term, trim off the IH, assuming it's an application *)
let trim_ih (trm : types) : types =
  assert (isApp trm);
  let (f, args) = destApp trm in
  let args_trim = Array.sub args 0 ((Array.length args) - 1) in
  mkApp (f, args_trim)

(* Given a diff, trim off the IHs, assuming the terms are applications *)
let trim_ihs (d : goal_proof_diff) : goal_proof_diff =
  let (old_term, new_term) = map_tuple trim_ih (proof_terms d) in
  eval_with_terms old_term new_term d

(* --- Casts --- *)

(* Given a difference in proofs, trim down any casts and get the terms *)
let rec erase_casts (d : goal_proof_diff) : goal_proof_diff =
  match kinds_of_terms (proof_terms d) with
  | (Cast (t, _, _), _) ->
     erase_casts (eval_with_old_term t d)
  | (_, Cast (t, _, _)) ->
     erase_casts (eval_with_new_term t d)
  | _ ->
     d

(* --- LetIn --- *)

(* Given a difference in proofs, substitute the head let ins *)
let simplify_letin (d : goal_proof_diff) : goal_proof_diff =
  let (o, n) = proof_terms d in
  if isLetIn o || isLetIn n then
    let d_dest = dest_goals d in
    let ((_, old_env), _) = old_proof d_dest in
    let ((_, new_env), _) = new_proof d_dest in
    let r = reduce_using reduce_whd_if_let_in in
    let o' = r old_env o in
    let n' = r new_env n in
    eval_with_terms o' n' d
  else
    d

(* --- Induction --- *)

(*
 * Given an ordered pair of lists of arrows to explore in the base case,
 * search the difference between each one.
 *
 * Stop as soon as we find a patch and return any of the patches.
 *
 * For now, we don't combine these in any way, and just look at the
 * difference between each pair, but without changing the goal type.
 * In the future we may want to be smarter about this.
 * All of the benchmarks so far work only with head, so it's unclear
 * what the recursive case should do so far. It might even be better
 * if it's just None like it used to be. Let's see where benchmarks
 * take us.
 *
 * The recursive call means that sometimes we'll end up with non-terms,
 * like the IHs, which not only can't be patches but will error
 * when we try to look. We should eliminate those from the list
 * before calling this.
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
let rec search_case_paths search opts (d : goal_case_diff) : types option =
  match diff_proofs d with
  | ((h1 :: t1), (h2 :: t2)) ->
     let d_goal = erase_proofs d in
     let d_t = add_to_diff d_goal t1 t2 in
     let ((_, env), _) = old_proof (dest_goals d) in
     (try
        let c1 = eval_proof_arrow h1 in
        let c2 = eval_proof_arrow h2 in
        let cs = search opts (add_to_diff d_goal c1 c2) in
        if List.length cs > 0 then
          let candidate = List.hd cs in
          match get_change opts with
          | InductiveType (_, _) ->
             Some candidate
          | FixpointCase ((_, _), cut) when are_cut env cut cs ->
             Some candidate
          | _ ->
             let lcs = try_lift_candidates reduce_strategies d_goal cs in
             if List.length lcs > 0 then
               Some (List.hd lcs)
             else
               search_case_paths search opts d_t
        else
          search_case_paths search opts d_t
      with _ ->
        search_case_paths search opts d_t)
  | (_, _) ->
     None

(*
 * Update the assumptions in a case of the inductive proof
 * Shift by the number of morphisms in the case,
 * assuming they are equal when they are convertible
 *)
let update_case_assums (d : proof_cat_diff) ms_o ms_n : equal_assumptions =
  List.fold_left2
    (fun assums dst_o dst_n ->
      let d_dest = difference dst_o dst_n assums in
      let (env, d_goal, _) = merge_lift_diff_envs d_dest [] in
      if convertible env (old_proof d_goal) (new_proof d_goal) then
        assume_local_equal assums
      else
        shift_assumptions assums)
    (assumptions d)
    (conclusions (remove_last ms_o))
    (conclusions (remove_last ms_n))

(*
 * Search a case of a difference in proof categories.
 * Return a patch if we find one.
 *
 * This breaks it up into arrows and then searches those
 * in the order of the sort function.
 *)
let search_case search opts sort (d : proof_cat_diff) : types option =
  let o = old_proof d in
  let n = new_proof d in
  let ms_o = morphisms o in
  let ms_n = morphisms n in
  search_case_paths
    search
    opts
    (reset_case_goals
       opts
       (map_diffs
          (fun (o, ms) -> (terminal o, ms))
          (always (update_case_assums d ms_o ms_n))
          (add_to_diff d (sort o ms_o) (sort n ms_n))))

(*
 * Base case: Prefer arrows later in the proof
 *)
let search_base_case search opts (d : proof_cat_diff) : types option =
  let sort _ ms = List.rev ms in
  search_case search (set_is_ind opts false) sort d

(*
 * Inductive case: Prefer arrows closest to an IH,
 * and in a tie, prefer arrows that are later.
 *
 * There currently may not be a guarantee that the two
 * arrows are traversed in exactly the same order for each proof.
 * If there is a bug in this, this may be why.
 *)
let search_inductive_case search opts (d : proof_cat_diff) : types option =
  let sort c ms = List.stable_sort (closer_to_ih c (find_ihs c)) ms in
  search_case search (set_is_ind opts true) sort d

(*
 * Search in a case, then adjust the patch so it type-checks
 * in the original envionment.
 *
 * If there is a bug here, then the unshift number may not generalize
 * for all cases.
 *)
let search_and_check_case search opts (d : proof_cat_diff) : types option =
  let o = expand_constr (old_proof d) in
  let n = expand_constr (new_proof d) in
  let assums = assumptions d in
  let d = difference o n assums in
  let offset =
    if is_conclusion (get_change opts) then
      List.length (morphisms o)
    else
      0
  in
  Option.map
    (unshift_by offset)
    (if has_ihs o then
       search_inductive_case search opts d
     else
       search_base_case search opts d)

(*
 * Search in a diff that has been broken up into different cases.
 * That is, search the base case, inductive case, and so on separately.
 *
 * For now, we only return the first patch we find.
 * We may want to return more later.
 *)
let rec search_and_check_cases search opts (ds : proof_cat_diff list) : candidates =
  match ds with
  | d :: tl ->
     let patch = search_and_check_case search opts d in
     if Option.has_some patch then
       [Option.get patch]
     else
       search_and_check_cases search opts tl
  | [] ->
     []

(*
 * Sort cs so that the base cases are first in the list
 * This is not yet tested
 * This is also not yet optimized
 *)
let base_cases_first (cs : proof_cat list) : proof_cat list =
  List.stable_sort
    (fun c1 c2 ->
      let c1_is_ind = has_ihs c1 in
      let c2_is_ind = has_ihs c2 in
      if c1_is_ind && not c2_is_ind then
        1
      else if not c2_is_ind && c1_is_ind then
        -1
      else
        0)
    cs

(*
 * Search an inductive proof for a patch.
 * That is, break it into cases, and search those cases for patches.
 *
 * This does not yet handle nested inducted proofs.
 * It needs to hook back into search to do that.
 *
 * This does not yet handle the case when the inductive parameters
 * are lists of different lengths, and this currently only searches for patches
 * that are for changes in conclusions.
 *)
let search_for_patch_inductive search opts (d : (proof_cat * int) proof_diff) : candidates =
  let (o, nparams) = old_proof d in
  let (n, nparams_n) = new_proof d in
  if not (nparams = nparams_n) then
    give_up
  else
    zoom_map
      (fun d ->
        let assums = assumptions d in
        let old_cases = base_cases_first (split (old_proof d)) in
        let new_cases = base_cases_first (split (new_proof d)) in
        let ds = dest_cases (difference old_cases new_cases assums) in
        List.map (unshift_by nparams) (search_and_check_cases search opts ds))
      []
      id
      (fun d ->
        intro_common
          (Option.get
             (List.fold_right2
                (fun pm1 pm2 (d : proof_cat_diff option) ->
                  let e1 = map_ext id pm1 in
                  let e2 = map_ext id pm2 in
                  let assums = assumptions (Option.get d) in
                  if extensions_equal_assums e1 e2 assums then
                    intro_common (Option.get d)
                  else
                    intro (Option.get d))
                (params (old_proof d) nparams)
                (params (new_proof d) nparams)
                (Some d))))
      (difference o n (assumptions d))

(* --- General proof terms --- *)

(*
 * Check if a term applies the inductive hypothesis
 * This is naive for now
 *)
let applies_ih opts (d : goal_proof_diff) : bool =
  map_if
    (fun (t1, t2) -> isApp t1 && isApp t2)
    (fun (t1, t2) ->
      let (f1, args1) = destApp t1 in
      let (f2, args2) = destApp t2 in
      let nargs1 = Array.length args1 in
      let nargs2 = Array.length args2 in
      let same_nargs = (nargs1 = nargs2) in
      is_ind opts && same_nargs && isLambda f1 && isLambda f2)
    (always false)
    (proof_terms d)

(*
 * Search for a direct patch given a difference in proof_cats within.
 * This is a collection of heuristics, which
 * we have numbered for clarity, and which we explain at the bottom
 * where it's closest to the code. Unimplemented heuristics
 * give_up (return the empty list).
 *
 * There is more work to make this generalize. For example, to handle
 * two proofs (f x) and (g y), where we can find (f -> g) and (y -> x),
 * we need to apply search_app as well. However, we don't always want to do
 * this, and doing this breaks some of our benchmark proofs. So when
 * we implement that benchmark, we need to consider how to determine
 * when to recurse that way. It's only immediately clear right now
 * for the inductive case in (3). Another missing example is
 * unwrapping function definitions. More missing features are in Trello.
 *
 * Heuristics, explained:
 * 1. When the proofs are definitionally equal, return the identity patch
 * 2a. When the proofs induct over the same hypotheses, then search
 *    the inductive proof for a patch, then get the leftover arguments.
 *    Apply a recursive patch for the first leftover argument,
 *    since it is the argument that induction occurred over.
 *    Ignore other hypotheses since our patch in the inductive case is direct.
 *    The "same hypothesis" depends on the kind of search: If it's a search
 *    for a difference in conclusions, then they must be exactly the same,
 *    but if it's for a difference in types, then they must be the same
 *    modulo those types (for now, they must be exactly those types).
 *    This heuristic is incomplete in its reasoning about leftover arguments.
 * 2b. When the condition for 2a holds but 2a fails, then treat it like 6a.
 * 3. When the proofs are inductive cases of a larger inductive proof,
 *    and we encounter a function that applies the inductive hypothesis,
 *    eliminate the IHs from the arguments and search
 *    for a patch recursively from function to function (forwards)
 *    and arguments to arguments (backwards).
 * 4. When both terms are lambdas, and there's a common argument
 *    type to both lambdas, then assume they are equal and zoom in.
 *    Look for a patch going from the common argument to the zoomed in
 *    term.
 * 5. When both terms are lambdas, there isn't a common argument,
 *    and we're either in the inductive case or dealing with a change,
 *    in types, then zoom in and search there like we would for common
 *    argument, but don't wrap it in a lambda (throw out the last argument).
 * 6a. When one proof term may apply the other and
 *    none of the other heuristics fire, then we use find_difference
 *    to try to find a direct patch by looking at the terms themselves.
 * 6b. When the condition for 6a holds but 6a fails, then treat it like 3.
 *)
let rec search (opts : options) (d : goal_proof_diff) : candidates =
  let d = erase_casts d in
  let d = simplify_letin d in
  let search_ind = search_for_patch_inductive search in
  if no_diff opts d then
    (*1*) identity_candidates d
  else if induct_over_same_h (same_h opts) d then
    (*2a*) let patches = search_app_ind search_ind search opts d in
    if List.length patches > 0 then
      patches
    else
      (*2b*) find_difference opts (proof_to_term d)
  else if applies_ih opts d then
    (*3*) search_app search search opts (trim_ihs d)
  else
    match kinds_of_terms (proof_terms d) with
    | (Lambda (n_o, t_o, b_o), Lambda (_, t_n, b_n)) ->
       if no_diff opts (eval_with_terms t_o t_n d) then
         (*4*) zoom_wrap_lambda search opts n_o t_o d
       else
         if is_ind opts || not (is_conclusion (get_change opts)) then
           (*5*) zoom_unshift search opts d
         else
           give_up
    | _ ->
       if is_app opts d then
         (*6a*) let patches = find_difference opts (proof_to_term d) in
         if List.length patches > 0 then
           patches
         else
           (*6b*) let patches = search_app search search opts d in
           if List.length patches > 0 then
             patches
           else
             (* 6c TODO explain, refactor, support better *)
             let (o, n) = proof_terms d in
             let d_red = reduce_diff reduce_term d in
             let (o_red, n_red) = proof_terms d_red in
             if not ((eq_constr o o_red) && (eq_constr n n_red)) then
               search opts d_red
             else
               give_up
       else
         give_up

(* Given a configuration, return the appropriate search function *)
let search_function (opts : options) (should_reduce : bool) =
  if should_reduce then
    (fun opts d -> search opts (reduce_diff reduce_term d))
  else
    search

(*
 * Determines final processing step for a patch candidate based on the
 * procedure/options.
 *
 * Mostly this is which components to call in the last
 * iteration of the "while not expanded" loop,
 * but it's messy because I had to workaround DeBruijn
 * inconsistencies and deal with user-cut lemmas
 * in the prototype. I'll fix this one day.
 *)
let return_patch (opts : options) (env : env) (patches : types list) =
  let flat_map f l = List.flatten (List.map f l) in
  match get_change opts with
  | FixpointCase ((old_type, new_type), cut) ->
     let body_reducer = specialize_in (get_app cut) specialize_term in
     let reduction_condition en tr = has_cut_type_strict_sym en cut tr in
     let reducer = reduce_body_if reduction_condition body_reducer in
     let specialized = List.map (reduce_using reducer env) patches in
     let specialized_fs = List.map (factor_term env) specialized in
     let specialized_fs_terms = flat_map reconstruct_factors specialized_fs in
     let specialized_typs = List.map (infer_type env) specialized_fs_terms in
     let p_typs = List.map (get_prop_type env) specialized_typs in
     let generalized = (* can simplify / try fewer *)
       flat_map
         (fun c ->
           flat_map
             (fun p_typ ->
               let goals = get_lifting_goals p_typ env old_type new_type in
               flat_map
                 (fun goal_type ->
                   let strategies = reduce_strategies_prop goal_type in
                   let (_, _, g) = destProd goal_type in
                   generalize_term strategies env c g)
                 goals)
             p_typs)
         specialized_fs_terms
     in List.hd generalized
  | ConclusionCase (Some cut) ->
     let patches = reduce_all remove_unused_hypos env patches in
     let generalized =
       flat_map
         (fun c ->
           let c_typs = List.map (infer_type env) [c] in
           let env_cut = push_rel (Anonymous, None, get_lemma cut) env in
           let (_, _, b) = destLambda (get_app cut) in
           let r = reduce_using reduce_remove_identities env in
           let g = r (get_lifting_goal_args 1 b) in
           generalize_term_args no_reduce_strategies env_cut (shift c) g)
         patches
     in List.hd generalized
  | _ ->
     Printf.printf "%s\n" "SUCCESS";
     List.hd patches

(*
 * The top-level search function!
 *
 * Search in one direction, and if we fail try the other direction.
 * If we find patches, return the head for now, since any patch will do.
 *)
let search_for_patch (default : types) (opts : options) (d : goal_proof_diff) : types =
  Printf.printf "%s\n\n" "----";
  let change = get_change opts in
  let d = if is_fixpoint_case change then reverse d else d in  (* explain *)
  let d = update_search_goals opts d (erase_goals d) in
  let should_reduce = is_inductive_type change in
  let search = search_function opts should_reduce in
  let patches = search opts d in
  let ((_, env), _) = old_proof (dest_goals d) in
  if List.length patches > 0 then
    return_patch opts env patches
  else
    let rev_patches = search opts (reverse d) in
    Printf.printf "%s\n" "searched backwards";
    Printf.printf "inverting %d candidates\n" (List.length rev_patches);
    let inverted = invert_terms invert_factor env rev_patches in
    match change with
    | Conclusion ->
       if List.length inverted > 0 then
         let patch = List.hd inverted in
         Printf.printf "%s\n" "SUCCESS";
         List.hd inverted
       else
         let patch = default in
         Printf.printf "%s\n" "FAILURE";
         patch
    | _ ->
       if List.length inverted > 0 then
         return_patch opts env inverted
       else
         failwith "Could not find patch"



