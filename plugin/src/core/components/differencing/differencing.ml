(* --- Differencing Component --- *)

open Searchopts
open Proofdiff
open Reducers
open Candidates
open Kindofchange
open Printing
open Catzooming
open Proofdifferencers
open Higherdifferencers
open Appdifferencers
open Inddifferencers
open Term
open Evd
open Utilities
open Constr
open Stateutils
open Proofcatterms

(* --- Debugging --- *)

(* Debug the search function *)
let debug_search (d : goal_proof_diff) : unit =
  let (t_o, t_n) = proof_terms d in
  let (g_o, _), (g_n, _), _ = d in
  let (typ_o, env_o), (typ_n, env_n) = map_tuple dest_context_term (g_o, g_n) in
  debug_term env_o t_o "old";
  debug_term env_n t_n "new";
  debug_term env_o typ_o "old goal";
  debug_term env_n typ_n "new goal";
  print_separator ()

(* --- Differencing --- *)

(* TODO temproary for refactor *)
let temp_to_diff assums envs terms goals sigma =
  let sigma, o = Evaluation.eval_proof (fst envs) (fst terms) sigma in
  let sigma, n = Evaluation.eval_proof (snd envs) (snd terms) sigma in
  let goal_o = Proofcat.Context (Proofcat.Term (fst goals, fst envs), fid ()) in
  let goal_n = Proofcat.Context (Proofcat.Term (snd goals, snd envs), fid ()) in
  let d = ((goal_o, o), (goal_n, n), assums) in
  sigma, d

let temp_from_diff d =
  let ((goal_o, o), (goal_n, n), assums) = d in
  let terms = map_tuple only_extension_as_term (o, n) in
  let goals = map_tuple dest_context_term (goal_o, goal_n) in
  let envs = map_tuple snd goals in
  let goals = map_tuple fst goals in
  (assums, envs, terms, goals)
                
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
 *    and we're either in the inductive case or dealing with a change
 *    in types or hypotheses, then zoom in and search there like we would for
 *    common argument, but don't wrap it in a lambda (throw out the last
 *    argument).
 * 6a. When one proof term may apply the other and
 *    none of the other heuristics fire, then we use find_difference
 *    to try to find a direct patch by looking at the terms themselves.
 * 6b. When the condition for 6a holds but 6a fails, then treat it like 3.
 * 6c. When 6b doesn't produce anything, try reducing the diff and calling
 *    recursively. (Support for this is preliminary.)
 *)
let rec diff opts assums envs terms goals sigma =
  let terms = reduce_casts terms in
  bind
    (reduce_letin envs terms)
    (fun terms ->
      branch_state
       (fun _ -> no_diff opts assums envs terms goals)
       (fun _ -> identity_candidates assums envs terms goals) (* 1 *)
       (fun _ ->
         branch_state
           (fun _ -> induct_over_same_h (same_h opts) assums envs terms)
           (fun _ ->
             try_chain_diffs
               [diff_app_ind (diff_inductive diff assums envs terms goals) diff opts; (* 2a *)
                find_difference opts] (* 2b *)
               assums
               envs
               terms
               goals)
           (fun _ ->
             if applies_ih opts terms then
               let terms = reduce_trim_ihs terms in
               diff_app diff diff opts assums envs terms goals (* 3 *)
             else
               match map_tuple kind terms with
               | (Lambda (n_o, t_o, b_o), Lambda (_, t_n, b_n)) ->
                  let change = get_change opts in
                  let ind = is_ind opts in
                  let is_id = is_identity change in
                  let search_body = to_search_function diff opts assums envs terms goals in
                  branch_state
                    (fun _ ->
                      no_diff
                        (if is_id then set_change opts Conclusion else opts)
                        assums
                        envs
                        (t_o, t_n)
                        goals)
                    (fun _ -> zoom_wrap_lambda search_body n_o t_o assums envs terms goals) (* 4 *)
                    (fun _ ->
                      let is_concl = is_conclusion change in
                      if ind || not (is_concl || is_id) then
                        zoom_unshift search_body assums envs terms goals (* 5 *)
                      else
                        ret give_up)
                    ()
               | _ ->
                  if is_app opts terms then
                    bind (* TODO move back into chaining, maybe *)
                      (find_difference opts assums envs terms goals) (* 6a *)
                      (fun cs ->
                        if non_empty cs then
                          ret cs
                        else
                          try_chain_diffs
                            [(diff_app diff diff opts);  (* 6b *)
                             (diff_reduced (diff opts))] (* 6c *)
                            assums
                            envs
                            terms
                            goals)
                  else
                    ret give_up)
           ())
       ())
    sigma
               
(* --- Top-level differencer --- *)

(* Given a configuration, return the appropriate differencer *)
let get_differencer (opts : options) assums envs terms goals sigma =
  let should_reduce = is_inductive_type (get_change opts) in
  if should_reduce then
    let sigma, term_o = reduce_term (fst envs) sigma (fst terms) in
    let sigma, term_n = reduce_term (snd envs) sigma (snd terms) in
    let terms = (term_o, term_n) in
    diff opts assums envs terms goals sigma
  else
    diff opts assums envs terms goals sigma
