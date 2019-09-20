(* --- Merging environments --- *)

open Constr
open Environ
open Debruijn
open Assumptions
open Utilities
open Contextutils
open Envutils

type closure = env * (types list)
type merged_closure = env * types list * types list

(* TODO needs cleanup, testing -- and when you test, see if you can change shifting to homogenous *)

(*
 * Merge two environments,
 * assuming certain terms are equal and substituting those equal terms
 *)
let merge_environments (env_o, env_n) assums =
  let num_rels = nb_rel env_o in
  let unshift_assums (a1, a2) = (unshift_from_assumptions_by num_rels a1, unshift_assumptions_by num_rels a2) in
  let split_assums = unshift_assums (split_assumptions assums env_o) in
  let (env_merged, _, _) =
    List.fold_left
       (fun (env, substs, l) i ->
         if has_assumption assums (mkRel i) then
           let shift_assums (a1, a2) = (shift_from_assumptions a1, shift_assumptions a2) in
           (env, shift_assums substs, l)
         else
           let shift_assums = map_tuple shift_assumptions in
           let decl = lookup_rel i env_o in
           let substitute = substitute_assumptions (fold_tuple union_assumptions substs) in
           let decl = CRD.map_constr substitute decl in
           (push_rel decl env, shift_assums substs, decl :: l))
       (env_n, split_assums, [])
       (List.rev (all_rel_indexes env_o))
  in env_merged

(*
 * Merge two closures (environments and lists of terms),
 * assuming certain terms are equal and substituting those equal terms
 *)
let merge_term_lists (env_o, env_n) (trms_o, trms_n) assums =
  let env = merge_environments (env_o, env_n) assums in
  let num_new_rels = new_rels2 env env_n in
  let shift_assums = shift_to_assumptions_by num_new_rels assums in
  let shift_non_assums =
    List.fold_left
      (fun s i ->
        if not (has_assumption assums (mkRel i)) then
          assume_local_equal (shift_assumptions s)
        else
          shift_from_assumptions s)
      no_assumptions
      (List.rev (all_rel_indexes env_o))
  in
  let to_substitute = union_assumptions shift_assums shift_non_assums in
  let trms_n = List.map (shift_by num_new_rels) trms_n in
  let trms_o = List.map (substitute_assumptions to_substitute) trms_o in
  (env, trms_o, trms_n)
       
(*
 * Merge two closures (environments and lists of terms),
 * assuming certain terms are equal and substituting those equal terms
 *)
let merge_terms envs (trm_o, trm_n) assums =
  let (env, trms_o, trms_n) = merge_term_lists envs ([trm_o], [trm_n]) assums in
  (env, List.hd trms_o, List.hd trms_n)

