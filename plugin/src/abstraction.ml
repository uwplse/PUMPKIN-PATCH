(*
 * Strategies for abstracting concrete terms
 * For now, since unification was unused, we simplify and don't use eterms
 * This makes the datatype easier to follow
 *
 * If we eventually need unification, we'll need to find a way to make the datatype
 * reasonable for that case, and add it back. See git history prior to
 * 6/23 to see how to do that.
 *)

open Term
open Environ
open Coqterms
open Collections
open Substitution
open Debruijn
open Printing

type abstracter = env -> types -> types -> types list -> types list
type abstraction_strategy = abstracter

(* TODO rename syntactic strategies, makes less sense given pattern *)

(* Fully abstract each term, substituting every convertible subterm *)
let syntactic_full (env : env) (arg_actual : types) (arg_abstract : types) (trms : types list) : types list =
  if eq_constr arg_actual arg_abstract then
    trms
  else
    List.map (all_conv_substs env (arg_actual, arg_abstract)) trms

let syntactic_full_strategy : abstraction_strategy =
  syntactic_full

(* Fully abstract each term, substituting every subterm w/ convertible types *)
let types_full (env : env) (arg_actual : types) (arg_abstract : types) (trms : types list) : types list =
  if eq_constr arg_actual arg_abstract then
    trms
  else
    List.map (all_typ_substs env (arg_actual, arg_abstract)) trms

let types_full_strategy : abstraction_strategy =
  types_full

(* A pattern-based full abstraction strategy for constructors *)
let pattern_full (env : env) (arg_actual : types) (arg_abstract : types) (trms : types list) : types list =
  let types_conv = types_convertible env arg_abstract in
  let exists_types_conv = List.exists types_conv in
  match map_tuple kind_of_term (arg_actual, arg_abstract) with
  | (App (f, args), _) when exists_types_conv (Array.to_list args) ->
     let arg = List.find types_conv (Array.to_list args) in
     let sub = all_constr_substs env f in
     syntactic_full env arg arg_abstract (List.map sub trms)
  | _ ->
     trms

let pattern_full_strategy : abstraction_strategy =
  pattern_full

(* All combinations of abstractions of convertible subterms *)
let syntactic_all_combinations (env : env) (arg_actual : types) (arg_abstract : types) (trms : types list) : types list =
  if eq_constr arg_actual arg_abstract then
    trms
  else
    List.flatten (List.map (all_conv_substs_combs env (arg_actual, arg_abstract)) trms)

let syntactic_all_strategy : abstraction_strategy =
  syntactic_all_combinations

(* Abstract the candidates by replacing actual args with abstract args, using an abstraction strategy  *)
let abstract_candidates (strategy : abstraction_strategy) (env : env) (args : types list) (args_abstract : types list) (cs : types list) : types list =
  let num_args = List.length args_abstract in
  if num_args > 0 then
    let cs_abs = strategy env (last args) (last args_abstract) cs in
    List.fold_right2
      (strategy env)
      (remove_last args)
      (remove_last args_abstract)
      cs_abs
  else
    []
