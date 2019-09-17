(* --- Change detectors --- *)

open Constr
open Environ
open Proofdiff
open Proofcatterms
open Cutlemma
open Kindofchange
open Reducers
open Assumptions
open Utilities
open Zooming
open Contextutils
open Convertibility
open Stateutils
open Envutils

(*
 * If the kind of change is a change in conclusion, then
 * determine whether the first different term is a constructor or
 * an induction principle.
 *
 * This is a heuristic and may sometimes be wrong, so we should
 * expose an option to users as well (TODO).
 *)
let find_kind_of_conclusion cut (trm_o, trm_n) =
  let rec configure trm_o trm_n =
    match map_tuple kind (trm_o, trm_n) with
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
 * Otherwise, if a single hypothesis has changed to a different hypothesis,
 * but it's not a type we are inducting over, then search for a change
 * in hypothesis.
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
  let env = context_env (old_proof d_goals) in
  let r t sigma = reduce_remove_identities env sigma t in
  let not_convertible =
    not_state (fun (t_o, t_n) sigma -> convertible env sigma t_o t_n)
  in
  let all_convertible =
    fold_tuple_state
      (forall2_state (fun t1 t2 sigma -> convertible env sigma t1 t2))
  in
  let rec diff env typ_o typ_n =
    match map_tuple kind (typ_o, typ_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       branch_state
         not_convertible
         (fun (t_o, t_n) ->
           let d_typs = difference t_o t_n no_assumptions in
           if same_shape env d_typs then
             ret (InductiveType (t_o, t_n))
           else
             let (t_o, t_n) = map_tuple (reconstruct_product env) (t_o, t_n) in
             ret (Hypothesis (t_o, t_n)))
         (fun (t_o, t_n) ->
           diff (push_local (n_o, t_o) env) b_o b_n)
         (t_o, t_n)
    | (App (f_o, args_o), App (f_n, args_n)) ->
       if (not (Array.length args_o = Array.length args_n)) then
         ret Conclusion
       else
         let args_o = Array.to_list args_o in
         let args_n = Array.to_list args_n in
         branch_state
           (and_state_fold
              (fun (f_o, f_n) -> ret (isConst f_o && isConst f_n))
              not_convertible)
           (fun (f_o, f_n) ->
             branch_state
               all_convertible
               (fun _ ->
                 if not (Option.has_some cut) then
                   failwith "Must supply cut lemma for change in fixpoint"
                 else
                   ret (FixpointCase ((f_o, f_n), Option.get cut)))
               (fun _ ->
                 ret Conclusion)
               (args_o, args_n))
           (fun (f_o, f_n) ->
             bind
               (map2_state (diff env) args_o args_n)
               (fun confs ->
                 if List.for_all is_conclusion confs then
                   ret Conclusion
                 else
                   ret (List.find (fun ch -> not (is_conclusion ch)) confs)))
           (f_o, f_n)
    | _ ->
       ret Conclusion
  in
  bind
    (map_tuple_state r (goal_types d_goals))
    (fun (old_goal, new_goal) ->
      bind
        (diff env old_goal new_goal)
        (fun change ->
          if is_conclusion change then
            ret (find_kind_of_conclusion cut (proof_terms d))
          else
            ret change))
