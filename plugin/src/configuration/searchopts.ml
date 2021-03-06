(* Search configuration *)

open Constr
open Environ
open Proofcat
open Proofcatterms
open Debruijn
open Utilities
open Proofdiff
open Assumptions
open Kindofchange
open Cutlemma
open Catzooming
open Indutils
open Contextutils
open Stateutils
open Convertibility
open Evd

(*
 * Note: Evar discipline is not good here yet, but will change when
 * we merge PUMPKIN with DEVOID and refactor.
 *)

(* --- Auxiliary --- *)

let terms_convertible env_o env_n src_o src_n =
  and_state
    (fun dst_o sigma -> convertible env_o sigma src_o dst_o)
    (fun dst_n sigma -> convertible env_n sigma src_n dst_n)

let context_envs = map_tuple context_env
let context_terms = map_tuple context_term

(* --- Options --- *)

(*
 * Options for search:
 * 1) The is_ind boolean determines when we are in the inductive
 *    case of an inductive proof and have just encountered two different
 *    inductive hypotheses. Right now it is very primitive; we may need a better
 *    condition to determine this later. This matters for some heuristics,
 *    which may fire when we don't want them to fire.
 * 2) The change field holds the kind of change we are searching for.
 * 3) The same_h function determines when two types we induct over are
      "the same" for the sake of search.
 * 4) The update_goals function takes in the old goals and an updated
 *    difference in proofs and adds updated goals to the difference in proofs.
 * 5) The is_app function determines whether one proof may be a function
 *    of the other proof.
 *
 * TODO update comment with other field explanations
 *)
type options =
  {
    is_ind : bool;
    change : kind_of_change;
    same_h : types -> types -> bool;
    update_goals : goal_proof_diff -> proof_cat_diff -> evar_map -> goal_proof_diff state;
    swap_goals : goal_term_diff -> goal_term_diff;
    reset_goals : goal_proof_diff -> goal_case_diff -> goal_case_diff;
    is_app : goal_proof_diff -> bool;
  }

type 'a configurable = options -> 'a

(* --- Configuring options --- *)

(*
 * Given a kind of change, configure the same_h function:
 * 1) If we are searching for a difference in types we are inducting over,
 *    then two types we induct over are "the same" if they are either identical
 *    or are the same as the types we changed.
 * 2) Otherwise, two types we induct over are "the same" if they are identical.
 *
 * POST-DEADLINE: No need for goals here, just need environments
 *)
let configure_same_h change (d : lift_goal_diff) : types -> types -> bool =
  match change with
  | InductiveType (o, n) ->
     let goals = (old_proof d, new_proof d) in
     let (env_o, env_n) = context_envs goals in
     (fun f_o f_n ->
       let k_o = destConst f_o in
       let k_n = destConst f_n in
       let ind_o = mkInd (Option.get (inductive_of_elim env_o k_o), 0) in
       let ind_n = mkInd (Option.get (inductive_of_elim env_n k_n), 0) in
       (equal f_o f_n) || (equal ind_o o && equal ind_n n))
  | _ ->
     equal

(*
 * Given a set of goals, update the goal terms for a change in types.
 * Eliminate the terms we encounter from the goal.
 *)
 let update_goal_terms goals rel_o rel_n =
   let (g_o, g_n) = context_terms goals in
   let (env_o, env_n) = context_envs goals in
   let env_o' = push_rel rel_o env_o in
   let env_n' = push_rel rel_n env_n in
   let (_, _, t_o) = CRD.to_tuple @@ rel_o in
   let (_, _, t_n) = CRD.to_tuple @@ rel_n in
   let trim = terms_convertible env_o' env_n' t_o t_n in
   match map_tuple kind (g_o, g_n) with
   | (Prod (_, t_g_o, b_o), Prod (_, t_g_n, b_n)) ->
      branch_state
	(trim t_g_o)
	(fun _ -> ret (Term (b_o, env_o'), Term (b_n, env_n')))
	(fun _ -> ret (Term (shift g_o, env_o'), Term (shift g_n, env_n')))
	t_g_n
   | _ ->
      ret (Term (shift g_o, env_o'), Term (shift g_n, env_n'))

(* Search for a difference in the changed constructor *)
let set_inductive_goals typ_o typ_n (d : 'a goal_diff) : 'a goal_diff =
  let (goal_o, proof_o) = old_proof d in
  let (goal_n, proof_n) = new_proof d in
  let assums = assumptions d in
  let env = context_env goal_o in
  let d_typs = difference typ_o typ_n no_assumptions in
  let d_constrs = ind_type_diff env d_typs in
  let (o, n) = (old_proof d_constrs, new_proof d_constrs) in
  let goal_o' = Context (Term (o, env), fid ()) in
  let goal_n' = Context (Term (n, env), fid ()) in
  difference (goal_o', proof_o) (goal_n', proof_n) assums

(*
 * Update the goals for a change in types
 *)
let update_goals_types d_old (d : proof_cat_diff) =
  let (old_goal, _) = old_proof d_old in
  let (new_goal, _) = new_proof d_old in
  match map_tuple kind (proof_terms d_old) with
  | (Lambda (n_o, t_o, _), Lambda (n_n, t_n, _)) ->
     let rel_o = CRD.LocalAssum(n_o, t_o) in
     let rel_n = CRD.LocalAssum(n_n, t_n) in
     bind
       (update_goal_terms (old_goal, new_goal) rel_o rel_n)
       (fun (g_o, g_n) ->
	 let o = (Context (g_o, fid ()), old_proof d) in
	 let n = (Context (g_n, fid ()), new_proof d) in
	 ret (difference o n (assumptions d)))
  | _ ->
     let o = (old_goal, old_proof d) in
     let n = (new_goal, new_proof d) in
     ret (difference o n (assumptions d))

(* Set goals for search for a difference in hypothesis *)
let set_hypothesis_goals t_o t_n (d : 'a goal_diff) : 'a goal_diff =
  let (goal_o, proof_o) = old_proof d in
  let (goal_n, proof_n) = new_proof d in
  let env_o = context_env goal_o in
  let env_n = context_env goal_n in
  let goal_o' = Context (Term (t_n, env_o), fid ()) in
  let goal_n' = Context (Term (t_o, env_n), fid ()) in
  difference (goal_o', proof_o) (goal_n', proof_n) (assumptions d)

(*
 * Given a change, determine how to update goals:
 * 1) If it's a change in a type we induct over,
 *    then update the environments and
 *    eliminate variables we encounter.
 * 2) If it's a change in hypotheses, update to the current hypotheses.
 * 3) Otherwise, update the goals to the current conclusions.
 *)
let configure_update_goals change d_old d =
  match change with
  | InductiveType (_, _) ->
     update_goals_types d_old d
  | Hypothesis (t_old, t_new) ->
     let d_def = add_goals d in
     let old_goals = map_tuple fst (old_proof d_old, new_proof d_old) in
     let default_goals = map_tuple fst (old_proof d_def, new_proof d_def) in
     let (g_o, g_n) = context_terms old_goals in
     let (g_o', g_n') = context_terms default_goals in
     if equal g_o g_o' && equal g_n g_n' then (* set initial goals *)
       ret (set_hypothesis_goals t_old t_new d_def)
     else (* update goals *)
       update_goals_types d_old d
  | _ ->
     ret (add_goals d)

(*
 * Given a change, determine how to test whether a proof might apply
 * another proof:
 * 1) If it's a change in types, then check whether the new proof
 *    may apply the old proof.
 * 2) If it's a change in conclusions or definitions,
 *    then check whether the old proof may apply the new proof.
 *)
let configure_is_app change d =
  match (map_tuple kind (proof_terms d), change) with
  | ((_, App (_, _)), InductiveType (_, _)) ->
     true
  | ((_, App (_, _)), Hypothesis (_, _)) ->
     true
  | ((App (_, _), _), _) ->
     true
  | _ ->
     false

(*
 * Given a change, determine the goals and proofs for testing whether a proof
 * might apply to another proof:
 * 1) If it's a change in inductive types or hypotheses, then swap the goals
 * 2) Otherwise, keep the goals as-is
 *)
let configure_swap_goals change d =
  match change with
  | (InductiveType (_, _)) | (Hypothesis (_, _)) ->
     swap_goals d
  | _ ->
     d

(*
 * Given options, determine how to reset the goals:
 *
 * 1) If it is a change in types, then search for a difference
 *    in the changed constructor.
 * 2) If it is a change in hypotheses, then search for a change in
 *    hypotheses
 * 3) Otherwise, search for the difference in conclusions.
 *
 * POST-DEADLINE:
 * This is for different inductive cases. It probably shouldn't
 * be separate from everything else, eventually need to refactor
 * all the goal-setting and resetting functions into a format that makes sense.
 *)
let configure_reset_goals change d_old (d : goal_case_diff) : goal_case_diff =
  match change with
  | InductiveType (typ_o, typ_n) ->
     set_inductive_goals typ_o typ_n d
  | Hypothesis (typ_o, typ_n) ->
     let (old_cases_goal, cases_o) = old_proof d in
     let (new_cases_goal, cases_n) = new_proof d in
     let env_o = context_env old_cases_goal in
     let env_n = context_env new_cases_goal in
     let (old_goal, _) = old_proof d_old in
     let (new_goal, _) = new_proof d_old in
     let num_new_rels_o = nb_rel env_o - nb_rel (context_env old_goal) in
     let num_new_rels_n = nb_rel env_n - nb_rel (context_env new_goal) in
     let o = shift_by num_new_rels_o (context_term old_goal) in
     let n = shift_by num_new_rels_n (context_term new_goal) in
     let goal_o = Context (Term (o, env_o), fid ()) in
     let goal_n = Context (Term (n, env_n), fid ()) in
     difference (goal_o, cases_o) (goal_n, cases_n) (assumptions d)
  | _ ->
     d

(*
 * Build configuration options for the search based on the goal diff
 *)
let configure_search d (change : kind_of_change) (cut : cut_lemma option) =
  {
    is_ind = false;
    change = change;
    same_h = configure_same_h change (erase_proofs d);
    update_goals = configure_update_goals change;
    swap_goals = configure_swap_goals change;
    reset_goals = configure_reset_goals change;
    is_app = configure_is_app change;
  }

(* --- Modifying options --- *)

let set_change opts change = { opts with change = change }
let set_is_ind opts is_ind = { opts with is_ind = is_ind }

(* --- Using options --- *)

let update_search_goals opts = opts.update_goals
let swap_search_goals opts = opts.swap_goals
let reset_case_goals opts = opts.reset_goals
let same_h opts = opts.same_h
let is_app opts = opts.is_app
let get_change opts = opts.change
let is_ind opts = opts.is_ind

(* Keep the same assumptions, but update the goals and terms for a diff *)
let update_terms_goals opts t_o t_n d =
  let update = update_search_goals opts d in
  bind
    (eval_with_terms t_o t_n d)
    (fun d -> update (erase_goals d))

(* Convert search to a search_function for zooming *)
let to_search_function search opts d =
  (fun d' -> 
    bind (update_search_goals opts d d') (search opts))

(*
 * Check if a term applies the inductive hypothesis
 * This is naive for now
 *)
let applies_ih opts (d : goal_proof_diff) : bool =
  match map_tuple kind (proof_terms d) with
  | (App (f1, args1), App (f2, args2)) ->
     is_ind opts && Array.length args1 = Array.length args2 && isLambda f1 && isLambda f2
  | _ ->
     false

