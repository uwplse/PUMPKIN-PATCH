(* --- Merging environments --- *)

open Term
open Environ
open Debruijn
open Assumptions
open Collections
open Coqterms
open Coqenvs

type merged_closure = env * types list * types list

(* TODO needs cleanup, testing -- and when you test, see if you can change shifting to homogenous *)

(*
 * Merge two environments,
 * assuming certain terms are equal and substituting those equal terms
 *)
let merge_environments (env1 : env) (env2 : env) (assums : equal_assumptions) : env =
  let num_rels = nb_rel env2 in
  let unshift_assums = map_tuple_hetero (unshift_from_assumptions_by num_rels) (unshift_assumptions_by num_rels) in
  let split_assums = unshift_assums (split_assumptions assums env2) in
  let (env_merged, _, _) =
    List.fold_left
       (fun (env, substs, l) i ->
         if has_assumption assums (mkRel i) then
           let shift_assums = map_tuple_hetero shift_from_assumptions shift_assumptions in
           (env, shift_assums substs, l)
         else
           let shift_assums = map_tuple shift_assumptions in
           let (n, b, t) = lookup_rel i env2 in
           let substitute = substitute_assumptions (fold_tuple union_assumptions substs) in
           let t' = substitute t in
           let b' = Option.map substitute b in
           (push_rel (n, b', t') env, shift_assums substs, (n, b', t') :: l))
       (env1, split_assums, [])
       (List.rev (all_rel_indexes env2))
  in env_merged

(*
 * Merge two closures (environments and lists of terms),
 * assuming certain terms are equal and substituting those equal terms
 *)
let merge_closures ((env1, trm1s) : closure) ((env2, trm2s) : closure) (assums : equal_assumptions) : merged_closure =
  let env_merged = merge_environments env1 env2 assums in
  let num_new_rels = (nb_rel env_merged) - (nb_rel env1) in
  let substitute = substitute_assumptions (shift_to_assumptions_by num_new_rels assums) in
  let trm1s_adj = List.map (shift_by num_new_rels) trm1s in
  let trm2s_subst = List.map substitute trm2s in
  (env_merged, trm1s_adj, trm2s_subst)
