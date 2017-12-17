(* --- Differencing Component --- *)

open Searchopts
open Proofdiff
open Coqterms
open Reducers
open Candidates
open Kindofchange
open Printing
open Zooming
open Proofdifferencers
open Higherdifferencers
open Appdifferencers
open Inddifferencers
open Proofcatterms

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
 * 6c. When 6b doesn't produce anything, try reducing the diff and calling
 *    recursively. (Support for this is preliminary.)
 *)
let rec diff (opts : options) (d : goal_proof_diff) : candidates =
  let d = reduce_letin (reduce_casts d) in
  if no_diff opts d then
    (*1*) identity_candidates d
  else if induct_over_same_h (same_h opts) d then
    try_chain_diffs
      [(diff_app_ind (diff_inductive diff) diff opts); (* 2a *)
       (find_difference opts)]                         (* 2b *)
      d
  else if applies_ih opts d then
    (*3*) diff_app diff diff opts (reduce_trim_ihs d)
  else
    match kinds_of_terms (proof_terms d) with
    | (Lambda (n_o, t_o, b_o), Lambda (_, t_n, b_n)) ->
       if no_diff opts (eval_with_terms t_o t_n d) then
         (*4*) zoom_wrap_lambda (to_search_function diff opts d) n_o t_o d
       else
         if is_ind opts || not (is_conclusion (get_change opts)) then
           (*5*) zoom_unshift (to_search_function diff opts d) d
         else
           give_up
    | _ ->
       if is_app opts d then
         try_chain_diffs
           [(find_difference opts);     (* 6a *)
            (diff_app diff diff opts);  (* 6b *)
            (diff_reduced (diff opts))] (* 6c *)
           d
       else
         give_up

(* --- Top-level differencer --- *)

(* Given a configuration, return the appropriate differencer *)
let get_differencer (opts : options) =
  let should_reduce = is_inductive_type (get_change opts) in
  if should_reduce then
    (fun d -> diff opts (reduce_diff reduce_term d))
  else
    diff opts
