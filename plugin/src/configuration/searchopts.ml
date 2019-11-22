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
open Envutils

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
 * TODO clean again before merge
 *)
type options =
  {
    is_ind : bool;
    change : kind_of_change;
    same_h : env -> constr -> constr -> evar_map -> bool state;
    update_goals : (env * env) -> (constr * constr) -> (types * types) -> (env * env) -> (constr * constr) -> evar_map -> ((env * env) * (constr * constr) * (types * types)) state;
    swap_proofs : (constr * constr) -> (constr * constr);
    reset_goals : (env * env) -> (types * types) -> (env * env) -> (types * types) -> ((env * env) * (types * types));
    is_app : (constr * constr) -> bool;
  }

type 'a configurable = options -> 'a

(* --- Configuring options --- *)

(*
 * Given a kind of change, configure the same_h function:
 * 1) If we are searching for a difference in types we are inducting over,
 *    then two types we induct over are "the same" if they are either identical
 *    or are the same as the types we changed.
 * 2) Otherwise, two types we induct over are "the same" if they are identical.
 *)
let configure_same_h change =
  match change with
  | InductiveType (o, n) ->
     (fun env f_o f_n ->
       let k_o = destConst f_o in
       let k_n = destConst f_n in
       let ind_o = mkInd (Option.get (inductive_of_elim env k_o), 0) in
       let ind_n = mkInd (Option.get (inductive_of_elim env k_n), 0) in
       ret ((equal f_o f_n) || (equal ind_o o && equal ind_n n)))
  | _ ->
     (fun env f_o f_n -> ret (equal f_o f_n))

(*
 * Given a set of goals, update the goal terms for a change in types.
 * Eliminate the terms we encounter from the goal.
 *)
let update_goal_terms envs terms goals =
  let (env_o, env_n) = envs in
  let (t_o, t_n) = terms in
  let trim = terms_convertible env_o env_n t_o t_n in
  let (g_o, g_n) = goals in
  match map_tuple kind (g_o, g_n) with
  | (Prod (_, t_g_o, b_o), Prod (_, t_g_n, b_n)) ->
     branch_state
       (trim t_g_o)
       (fun _ -> ret (b_o, b_n))
       (fun _ -> ret (map_tuple shift (g_o, g_n)))
       t_g_n
  | _ ->
     ret (map_tuple shift (g_o, g_n))

(* Search for a difference in the changed constructor *)
let set_inductive_goals envs (typ_o, typ_n) =
  let env = fst envs in
  let d_typs = typ_o, typ_n, no_assumptions in
  let (o, n, _) = ind_type_diff env d_typs in
  (env, env), (o, n)

(*
 * Update the goals for a change in types
 * TODO: can we match over goals and use product instead?
 *)
let zoom_goals envs terms goals =
  match map_tuple kind terms with
  | (Lambda (n_o, t_o, _), Lambda (n_n, t_n, _)) ->
     let env_o, env_n = envs in
     let envs = push_local (n_o, t_o) env_o, push_local (n_n, t_n) env_n in
     let terms = t_o, t_n in
     bind
       (update_goal_terms envs terms goals)
       (fun goals ->
         ret (envs, goals))
  | _ ->
     ret (envs, goals)

(*
 * Given a change, determine how to update goals:
 * 1) If it's a change in a type we induct over,
 *    then update the environments and
 *    eliminate variables we encounter.
 * 2) If it's a change in hypotheses, update to the current hypotheses.
 * 3) Otherwise, update the goals to the current conclusions.
 *)
let configure_update_goals change envs terms goals envs_next terms_next sigma =
  let sigma, goal_o = Inference.infer_type (fst envs_next) sigma (fst terms_next) in
  let sigma, goal_n = Inference.infer_type (snd envs_next) sigma (snd terms_next) in
  let goals_next = (goal_o, goal_n) in
  bind
    (match change with
    | InductiveType (_, _) ->
       zoom_goals envs terms goals
    | Hypothesis (t_old, t_new) ->
       let (g_o, g_n) = goals in
       let (g_o', g_n') = goals_next in
       if equal g_o g_o' && equal g_n g_n' then (* set initial goals *)
         let envs = (snd envs_next, fst envs_next) in
         let goals = (t_new, t_old) in
         ret (envs, goals)
       else (* update goals *)
         zoom_goals envs terms goals
    | _ ->
       ret (envs_next, goals_next))
    (fun (envs, goals) ->
      ret (envs, terms_next, goals))
    sigma
  
(*
 * Given a change, determine how to test whether a proof might apply
 * another proof:
 * 1) If it's a change in types, then check whether the new proof
 *    may apply the old proof.
 * 2) If it's a change in conclusions or definitions,
 *    then check whether the old proof may apply the new proof.
 *)
let configure_is_app change terms =
  match (map_tuple kind terms, change) with
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
let configure_swap_proofs change (trm_o, trm_n) =
  match change with
  | (InductiveType (_, _)) | (Hypothesis (_, _)) ->
     (trm_n, trm_o)
  | _ ->
     (trm_o, trm_n)

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
 *
 * TODO naming etc
 *)
let configure_reset_goals change envs_old goals_old envs goals =
  match change with
  | InductiveType (typ_o, typ_n) ->
     set_inductive_goals envs (typ_o, typ_n)
  | Hypothesis (typ_o, typ_n) ->
     let num_new_rels_o = new_rels2 (fst envs) (fst envs_old) in
     let num_new_rels_n = new_rels2 (snd envs) (snd envs_old) in
     let goal_o = shift_by num_new_rels_o (fst goals_old) in
     let goal_n = shift_by num_new_rels_n (snd goals_old) in
     envs, (goal_o, goal_n)
  | _ ->
     envs, goals

(*
 * Build configuration options for the search based on the goal diff
 *)
let configure_search change cut =
  {
    is_ind = false;
    change = change;
    same_h = configure_same_h change;
    update_goals = configure_update_goals change;
    swap_proofs = configure_swap_proofs change;
    reset_goals = configure_reset_goals change;
    is_app = configure_is_app change;
  }

(* --- Modifying options --- *)

let set_change opts change = { opts with change = change }
let set_is_ind opts is_ind = { opts with is_ind = is_ind }

(* --- Using options --- *)

let update_search_goals opts = opts.update_goals
let swap_search_proofs opts = opts.swap_proofs
let reset_case_goals opts = opts.reset_goals
let same_h opts = opts.same_h
let is_app opts = opts.is_app
let get_change opts = opts.change
let is_ind opts = opts.is_ind

(* Convert search to a search_function for zooming *)
let to_search_function search opts assums envs terms goals =
  (fun d' ->
    let (o, n, assums) = d' in
    let terms_next = map_tuple only_extension_as_term (o, n) in (* TODO is this different from terms? *)
    let envs_next = map_tuple context_env (map_tuple terminal (o, n)) in
    bind
      (update_search_goals opts envs terms goals envs_next terms_next)
      (fun (envs, terms, goals) sigma ->
        search opts assums envs terms goals sigma))

(*
 * Check if a term applies the inductive hypothesis
 * This is naive for now
 *)
let applies_ih opts terms : bool =
  match map_tuple kind terms with
  | (App (f1, args1), App (f2, args2)) ->
     is_ind opts && Array.length args1 = Array.length args2 && isLambda f1 && isLambda f2
  | _ ->
     false

