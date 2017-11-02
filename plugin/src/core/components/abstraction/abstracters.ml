(* --- Abstraction Strategies --- *)

open Term
open Environ
open Coqterms
open Collections
open Substitution
open Debruijn
open Printing
open Specialization
open Filters

type candidates = types list

type abstraction_dimension = Arguments | Property of types
type abstracter = env -> types -> types -> candidates -> candidates

type abstraction_strategy =
  {
    reducer : reducer;
    abstracter : abstracter;
    filter : types filter_strategy;
    to_abstract : abstraction_dimension;
  }

(* --- Top-level --- *)

(*
 * Substitute actual args with abstract args in candidates,
 * using an abstracter to determine when to substitute.
 *)
let substitute_using (strategy : abstraction_strategy) (env : env) (args : types list) (args_abstract : types list) (cs : candidates) : candidates =
  let abs = strategy.abstracter in
  let num_args = List.length args_abstract in
  if num_args > 0 then
    let cs_abs = abs env (last args) (last args_abstract) cs in
    List.fold_right2
      (abs env)
      (remove_last args)
      (remove_last args_abstract)
      cs_abs
  else
    []

(*
 * Reduce using the reducer in the abstraction strategy
 *)
let reduce_all_using strategy (env : env) (cs : candidates) : candidates =
  reduce_all strategy.reducer env cs

(*
 * Filter using the filter in the abstraction stragegy
 *)
let filter_using strategy env (goal : types) (cs : candidates) : candidates =
  strategy.filter env goal cs

(* --- Recover options from an abstraction strategy --- *)

let kind_of_abstraction strategy = strategy.to_abstract

(* --- Abstracters --- *)

(*
 * Abstracters determine how to perform the substitution step of abstraction
 *)

(* TODO rename syntactic strategies, makes less sense given pattern *)

(* Fully abstract each term, substituting every convertible subterm *)
let syntactic_full (env : env) (arg_actual : types) (arg_abstract : types) (trms : candidates) : candidates =
  if eq_constr arg_actual arg_abstract then
    trms
  else
    List.map (all_conv_substs env (arg_actual, arg_abstract)) trms

let syntactic_full_strategy : abstracter =
  syntactic_full

(* Fully abstract each term, substituting every subterm w/ convertible types *)
let types_full (env : env) (arg_actual : types) (arg_abstract : types) (trms : candidates) : candidates =
  if eq_constr arg_actual arg_abstract then
    trms
  else
    List.map (all_typ_substs env (arg_actual, arg_abstract)) trms

let types_full_strategy : abstracter =
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

let pattern_full_strategy : abstracter =
  pattern_full

(* All combinations of abstractions of convertible subterms *)
let syntactic_all_combinations (env : env) (arg_actual : types) (arg_abstract : types) (trms : candidates) : candidates =
  if eq_constr arg_actual arg_abstract then
    trms
  else
    List.flatten (List.map (all_conv_substs_combs env (arg_actual, arg_abstract)) trms)

let syntactic_all_strategy : abstracter =
  syntactic_all_combinations

(* --- Strategies for abstracting arguments --- *)

(*
 * Reduce first
 * Replace all convertible terms at the highest level with abstracted terms
 *)
let syntactic_full_reduce : abstraction_strategy =
  {
    reducer = reduce_remove_identities;
    abstracter = syntactic_full_strategy;
    filter = filter_by_type;
    to_abstract = Arguments;
  }

(*
 * Don't reduce
 * Replace all convertible terms at the highest level with abstracted terms
 *)
let syntactic_full_no_reduce : abstraction_strategy =
  {syntactic_full_reduce with reducer = remove_identities; }

(*
 * Reduce first
 * Replace all terms with convertible types at the highest level
 * with abstracted terms
 *)
let types_full_reduce : abstraction_strategy =
  {
    reducer = reduce_remove_identities;
    abstracter = types_full_strategy;
    filter = filter_by_type;
    to_abstract = Arguments;
  }

(*
 * Don't reduce
 * Replace all convertible terms at the highest level with abstracted terms
 *)
let types_full_no_reduce : abstraction_strategy =
  { types_full_reduce with reducer = remove_identities; }

(*
 * Reduce first
 * Replace all terms matching a pattern (f, args) with abstracted terms
 * Fall back to syntactic_full when the concrete argument is not a pattern
 *)
let pattern_full_reduce : abstraction_strategy =
  {
    reducer = reduce_remove_identities;
    abstracter = pattern_full_strategy;
    filter = filter_by_type;
    to_abstract = Arguments;
  }

(*
 * Don't reduce
 * Replace all terms matching a pattern (f, args) with abstracted terms
 * Fall back to syntactic_full when the concrete argument is not a pattern
 *)
let pattern_no_reduce : abstraction_strategy =
  { pattern_full_reduce with reducer = remove_identities; }

(*
 * Reduce first
 * Replace all combinations of convertible subterms with abstracted terms
 *)
let syntactic_all_reduce : abstraction_strategy =
  {
    reducer = reduce_remove_identities;
    abstracter = syntactic_all_strategy;
    filter = filter_by_type;
    to_abstract = Arguments;
  }

(*
 * Don't reduce
 * Replace all combinations of convertible subterms with abstracted terms
 *)
let syntactic_all_no_reduce : abstraction_strategy =
  { syntactic_all_reduce with reducer = remove_identities; }

(*
 * All strategies that reduce first
 *)
let reduce_strategies : abstraction_strategy list =
  [syntactic_full_reduce; syntactic_all_reduce; pattern_full_reduce]

(*
 * All strategies that don't reduce first
 *)
let no_reduce_strategies : abstraction_strategy list =
  [syntactic_full_no_reduce; syntactic_all_no_reduce; pattern_no_reduce]

(*
 * List of default strategies
 *)
let default_strategies : abstraction_strategy list =
  [syntactic_full_no_reduce; syntactic_full_reduce; pattern_full_reduce;
   syntactic_all_no_reduce; syntactic_all_reduce; pattern_no_reduce]

(*
 * List of the simplest strategies
 *)
let simple_strategies : abstraction_strategy list =
  [syntactic_full_reduce; syntactic_full_no_reduce]

(* --- Strategies for abstracting properties --- *)

let types_full_reduce_prop (goal : types) : abstraction_strategy =
  { types_full_reduce with to_abstract = Property goal; }

let types_full_no_reduce_prop (goal : types) : abstraction_strategy =
  { types_full_no_reduce with to_abstract = Property goal; }

let reduce_strategies_prop (goal : types) : abstraction_strategy list =
  [types_full_reduce_prop goal]

let no_reduce_strategies_prop (goal : types) : abstraction_strategy list =
  [types_full_no_reduce_prop goal]

let default_strategies_prop (goal : types) : abstraction_strategy list =
  List.append
    (reduce_strategies_prop goal)
    (no_reduce_strategies_prop goal)
