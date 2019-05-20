(* --- Merging environments --- *)

open Constr
open Environ
open Debruijn
open Assumptions
open Utilities
open Coqterms

module CRD = Context.Rel.Declaration

type merged_closure = env * types list * types list

(* TODO needs cleanup, testing -- and when you test, see if you can change shifting to homogenous *)

(*
 * Merge two environments,
 * assuming certain terms are equal and substituting those equal terms
 *)
let merge_environments (env1 : env) (env2 : env) (assums : equal_assumptions) : env =
  let num_rels = nb_rel env2 in
  let unshift_assums (a1, a2) = (unshift_from_assumptions_by num_rels a1, unshift_assumptions_by num_rels a2) in
  let split_assums = unshift_assums (split_assumptions assums env2) in
  let (env_merged, _, _) =
    List.fold_left
       (fun (env, substs, l) i ->
         if has_assumption assums (mkRel i) then
           let shift_assums (a1, a2) = (shift_from_assumptions a1, shift_assumptions a2) in
           (env, shift_assums substs, l)
         else
           let shift_assums = map_tuple shift_assumptions in
           let decl = lookup_rel i env2 in
           let substitute = substitute_assumptions (fold_tuple union_assumptions substs) in
           let decl = CRD.map_constr substitute decl in
           (push_rel decl env, shift_assums substs, decl :: l))
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
  let shift_assums = shift_to_assumptions_by num_new_rels assums in
  let shift_non_assums =
    List.fold_left
      (fun s i ->
        if not (has_assumption assums (mkRel i)) then
          assume_local_equal (shift_assumptions s)
        else
          shift_from_assumptions s)
      no_assumptions
      (List.rev (all_rel_indexes env2))
  in
  let to_substitute = union_assumptions shift_assums shift_non_assums in
  let trm1s_adj = List.map (shift_by num_new_rels) trm1s in
  let trm2s_subst = List.map (substitute_assumptions to_substitute) trm2s in
  (env_merged, trm1s_adj, trm2s_subst)
