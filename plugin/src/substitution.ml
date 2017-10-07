(* Substitution auxiliary functions *)

open Environ
open Term
open Coqterms
open Hofs
open Assumptions
open Debruijn
open Coqterms
open Coqenvs
open Assumptions
open Debruijn
open Collections
open Printing

(* TODO clean up so retrieval is easier *)
type merged_closure = env * types list * types list
type ('a, 'b) substitution = env -> 'a -> types -> 'b
type 'a comb_substitution = ('a, types list) substitution
type 'a type_substitution = ('a, types) substitution

(* Map a substitution over a term *)
let all_substs p env (src, dst) trm : types =
  map_term_env_if
    (fun en (s, _) t -> p en s t)
    (fun _ (_, d) _ -> d)
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm

(* Map all combinations of a substitution over a term *)
let all_substs_combs p env (src, dst) trm : types list =
  map_subterms_env_if
    (fun en (s, _) t -> p en s t)
    (fun _ (_, d) t -> [d; t])
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm

(* In env, substitute all subterms of trm that are convertible to src with dst *)
let all_conv_substs : (types * types) type_substitution =
  all_substs convertible

(* In env, substitute all subterms of trm that have a convertible type to the type of src with dst *)
let all_typ_substs : (types * types) type_substitution =
  all_substs types_convertible

(*
 * Check if a subterm matches applies a constructor function pat to
 * an argument with the type of itself
 *)
let constructs_recursively env c trm : bool =
  if isApp trm then
    try
      let (f, args) = destApp trm in
      let conv = convertible env in
      let types_conv = types_convertible env in
      conv f c && List.exists (types_conv trm) (Array.to_list args)
    with _ ->
      false
  else
    false

(*
 * Map a constructor substitution over a term
 * The constructor is a function c
 * This finds the outermost applications of c to an argument
 * with the type of the term itself, "undoing" the constructor
 * It substitutes in the first argument with that type
 *
 * Can generalize this further
 *)
let all_constr_substs env c trm : types =
  map_term_env_if
    constructs_recursively
    (fun _ _ t ->
      let (_, args_t) = destApp t in
      List.find (types_convertible env t) (Array.to_list args_t))
    shift
    env
    c
    trm

(* In env, return all substitutions of subterms of trm that are convertible to src with dst *)
let all_conv_substs_combs : (types * types) comb_substitution =
  all_substs_combs convertible

(* In env, return all substitutions of subterms of trm that have a convertible type to the type of src with dst *)
let all_typ_substs_combs : (types * types) comb_substitution =
  all_substs_combs types_convertible

(*
 * Get a swap map for all combinations of a function application
 *)
let build_swap_map (en : env) (t : types) : swap_map =
  match kind_of_term t with
  | App (_, args) ->
     filter_swaps
       (fun (a1, a2) ->
	 (not (convertible en a1 a2)) && types_convertible en a1 a2)
       (combinations_of_arguments args)
  | _ ->
     no_swaps

(*
 * Given a pair of arguments to swap, apply the swap inside of args
 *)
let swap_args (env : env) (args : types array) ((a1, a2) : types * types) =
  combine_cartesian_append
    (Array.map
       (fun a ->
         if convertible env a1 a then
           [a2]
         else if convertible env a2 a then
           [a1]
         else
           [a])
       args)

(*
 * Apply a swap map to an array of arguments
 *)
let apply_swaps env args swaps : (types array) list =
  List.flatten (map_swaps (swap_args env args) swaps)

(*
 * Apply a swap map to an array of arguments,
 * then combine the results using the combinator c, using a as a default
 *)
let apply_swaps_combine c a env args swaps : 'a list =
  let swapped = apply_swaps env args swaps in
  if List.length swapped = 0 then
    [a]
  else
    a :: List.map c swapped

(* In env, swap all arguments to a function
 * with convertible types with each other, building a swap map for each
 * term
 *)
let all_typ_swaps_combs (env : env) (trm : types) : types list =
  unique
    eq_constr
    (map_subterms_env_if_lazy
       (fun en _ t  ->
         isApp t)
       (fun en _ t ->
	 let swaps = build_swap_map en t in
	 let (f, args) = destApp t in
	 apply_swaps_combine (fun s -> mkApp (f, s)) t env args swaps)
       (fun _ -> ())
       env
       ()
       trm)

(*
 * In an environment, swaps all subterms  convertible to the source
 * and destination terms in the swap map with each other.
 *
 * This checks convertibility before recursing, and so will replace at
 * the highest level possible.
 *)
let all_conv_swaps_combs (env : env) (swaps : swap_map) (trm : types) =
    unique
    eq_constr
    (map_subterms_env_if_lazy
       (fun _ _ t  -> isApp t)
       (fun en depth t ->
	 let swaps = shift_swaps_by depth swaps in
	 let (f, args) = destApp t in
	 unique
	   eq_constr
	   (apply_swaps_combine (fun s -> mkApp (f, s)) t env args swaps))
       (fun depth -> depth + 1)
       env
       0
       trm)

(* Apply assums in trm *)
let substitute_assumptions (assums : equal_assumptions) (trm : types) : types =
  map_term_if
    has_assumption
    get_assumption
    shift_assumptions
    assums
    trm

(* Substitute provided indexes in trm with associated terms in subs *)
let substitute_params (subs : param_substitutions) (trm : types) : types =
  map_term_if
    has_substitution
    get_substitution
    shift_substitutions
    subs
    trm

(* Substitute provided indexes in an environment with the provided terms *)
let substitute_env_params (subs : param_substitutions) (env : env) : env =
  let num_rels = nb_rel env in
  let all_rels = List.rev (lookup_all_rels env) in
  snd
    (List.fold_left
     (fun (s, env) (n, b, t) ->
       let sub = substitute_params s in
       (shift_substitutions s, push_rel (n, Option.map sub b, sub t) env))
     (unshift_substitutions_by num_rels subs, pop_rel_context num_rels env)
     all_rels)

(* --- Merging environments --- *)

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

