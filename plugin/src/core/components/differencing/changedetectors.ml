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
let find_kind_of_change evd (cut : cut_lemma option) (d : goal_proof_diff) =
  let d_goals = erase_proofs d in
  let goals = goal_types d_goals in
  let env = context_env (old_proof d_goals) in
  let r = reduce_remove_identities env evd in
  let _, old_goal = r (fst goals) in
  let _, new_goal = r (snd goals) in
  let rec diff env typ_o typ_n =
    match map_tuple kind (typ_o, typ_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if (not (snd (convertible env evd t_o t_n))) then
         let d_typs = difference t_o t_n no_assumptions in
         if same_shape env d_typs then
           InductiveType (t_o, t_n)
         else
           let (t_o', t_n') = map_tuple (reconstruct_product env) (t_o, t_n) in
           Hypothesis (t_o', t_n')
       else
         diff (push_rel CRD.(LocalAssum(n_o, t_o)) env) b_o b_n
    | (App (f_o, args_o), App (f_n, args_n)) ->
       if (not (Array.length args_o = Array.length args_n)) then
         Conclusion
       else
         let args_o = Array.to_list args_o in
         let args_n = Array.to_list args_n in
         if isConst f_o && isConst f_n && (not (snd (convertible env evd f_o f_n))) then
           if List.for_all2 (fun t1 t2 -> snd (convertible env evd t1 t2)) args_o args_n then
             if not (Option.has_some cut) then
               failwith "Must supply cut lemma for change in fixpoint"
             else
               FixpointCase ((f_o, f_n), Option.get cut)
           else
             Conclusion
         else
           let arg_confs = List.map2 (diff env) args_o args_n in
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
