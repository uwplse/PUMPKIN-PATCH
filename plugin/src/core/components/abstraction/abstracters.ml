(* --- Abstraction Strategies --- *)

open Constr
open Environ
open Evd
open Utilities
open Substitution
open Reducers
open Filters
open Candidates
open Convertibility

type abstraction_dimension = Arguments | Property
type abstracter = env -> evar_map -> types -> types -> candidates -> candidates

type abstraction_strategy =
  {
    reducer : reducer;
    abstracter : abstracter;
    filter : types -> types filter_strategy;
    to_abstract : abstraction_dimension;
  }

(* --- Auxiliary functions --- *)

(*
 * Count the number of applications in a term.
 * Do not consider lambdas.
 *)
let rec num_apps (trm : types) : int =
  match kind trm with
  | App (f, args) ->
     Array.fold_left (fun n a -> n + num_apps a) (1 + num_apps f) args
  | _ ->
     0

(*
 * Heuristic for sorting the arguments to decide which ones to abstract first.
 * Treats terms with more applications as larger.
 *)
let sort_dependent args args_abstract =
  List.split
    (List.stable_sort
       (fun (a1, _) (a2, _) -> num_apps a1 - num_apps a2)
       (List.combine args args_abstract))

(* --- Top-level --- *)

(*
 * Substitute actual args with abstract args in candidates,
 * using an abstracter to determine when to substitute.
 *)
let substitute_using (strategy : abstraction_strategy) (env : env) (evd : evar_map) (args : types list) (args_abstract : types list) (cs : candidates) : candidates =
  let abs = strategy.abstracter in
  let num_args = List.length args_abstract in
  let (args_sorted, args_abstract_sorted) = sort_dependent args args_abstract in
  if num_args > 0 then
    let cs_abs = abs env evd (last args_sorted) (last args_abstract_sorted) cs in
    List.fold_right2
      (abs env evd)
      (all_but_last args_sorted)
      (all_but_last args_abstract_sorted)
      cs_abs
  else
    []

(*
 * Reduce using the reducer in the abstraction strategy
 *)
let reduce_all_using strategy env evd (cs : candidates) : candidates =
  reduce_all strategy.reducer env evd cs

(*
 * Filter using the filter in the abstraction stragegy
 *)
let filter_using strategy env evd (goal : types) (cs : candidates) : candidates =
  strategy.filter goal env evd cs

(* --- Recover options from an abstraction strategy --- *)

let kind_of_abstraction strategy = strategy.to_abstract

(* --- Abstracters --- *)

(*
 * Abstracters determine how to perform the substitution step of abstraction
 *)

(* TODO rename syntactic strategies, makes less sense given pattern *)

(* Fully abstract each term, substituting every convertible subterm *)
let syntactic_full env evd (arg_actual : types) (arg_abstract : types) (trms : candidates) : candidates =
  if equal arg_actual arg_abstract then
    trms
  else
    List.map (all_conv_substs env evd (arg_actual, arg_abstract)) trms

let syntactic_full_strategy : abstracter =
  syntactic_full

(* Fully abstract each term, substituting every subterm w/ convertible types *)
let types_full env evd (arg_actual : types) (arg_abstract : types) (trms : candidates) : candidates =
  if equal arg_actual arg_abstract then
    trms
  else
    List.map (all_typ_substs env evd (arg_actual, arg_abstract)) trms

let types_full_strategy : abstracter =
  types_full

(* A pattern-based full abstraction strategy for functions *)
(* TODO really just need a more flexible top-level function that lets you combine strategies *)
let function_pattern_full (env : env) (evd : evar_map) (arg_actual : types) (arg_abstract : types) (trms : types list) : types list =
  match kind arg_abstract with
  | App (f, args) ->
     syntactic_full env evd arg_actual arg_abstract trms
  | _ ->
     types_full env evd arg_actual arg_abstract trms

let function_pattern_full_strategy : abstracter =
  function_pattern_full

(* A pattern-based full abstraction strategy for constructors *)
let pattern_full (env : env) (evd : evar_map) (arg_actual : types) (arg_abstract : types) (trms : types list) : types list =
  let types_conv = types_convertible env evd arg_abstract in
  let exists_types_conv = List.exists types_conv in
  match map_tuple kind (arg_actual, arg_abstract) with
  | (App (f, args), _) when exists_types_conv (Array.to_list args) ->
     let arg = List.find types_conv (Array.to_list args) in
     let sub = all_constr_substs env evd f in
     syntactic_full env evd arg arg_abstract (List.map sub trms)
  | _ ->
     trms

let pattern_full_strategy : abstracter =
  pattern_full

(* All combinations of abstractions of convertible subterms *)
let syntactic_all_combinations env evd (arg_actual : types) (arg_abstract : types) (trms : candidates) : candidates =
  if equal arg_actual arg_abstract then
    trms
  else
    flat_map (all_conv_substs_combs env evd (arg_actual, arg_abstract)) trms

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
 * Replace functions with abstracted functions when types are convertible
 * Replace applications with abstracted applications when terms are convertible 
 *)
let function_pattern_full_reduce : abstraction_strategy =
  {
    reducer = reduce_remove_identities;
    abstracter = function_pattern_full_strategy;
    filter = filter_by_type;
    to_abstract = Arguments;
  }

(*
 * Don't reduce
 * Otherwise act like function_pattern_no_reduce
 *)
let function_pattern_full_no_reduce : abstraction_strategy =
  { function_pattern_full_reduce with reducer = remove_identities; }

    
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

let function_pattern_full_reduce_prop : abstraction_strategy =
  { function_pattern_full_reduce with to_abstract = Property }

let function_pattern_full_no_reduce_prop : abstraction_strategy =
  { function_pattern_full_no_reduce with to_abstract = Property }

let reduce_strategies_prop : abstraction_strategy list =
  [function_pattern_full_reduce_prop]

let no_reduce_strategies_prop : abstraction_strategy list =
  [function_pattern_full_no_reduce_prop]

let default_strategies_prop : abstraction_strategy list =
  List.append reduce_strategies_prop no_reduce_strategies_prop

