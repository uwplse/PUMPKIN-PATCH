(* Equality assumptions for substitutions in proof search *)

open Constr
open Environ
open Utilities
open Debruijn
open Coqterms
open Hofs
open Printing

module CRD = Context.Rel.Declaration

(* For now, these are lists of pairs of ints, each int representing
   an index in a different environment; this representation
   is hard to use, so may change this in the future (TODO) *)

type equal_assumptions = (int * int) list
type param_substitutions = (int * types) list
type swap_map = (types * types) list

let no_assumptions = []
let no_substitutions = []
let no_swaps = []

(* --- Auxiliary functions on assumptions --- *)

(* Print a list of substitutions for debugging purposes *)
let substitutions_as_string (env : env) (subs : param_substitutions) : string =
  String.concat
    ",\n"
    (List.map
       (fun (i, trm) ->
         Printf.sprintf "(%d, %s)" i (term_as_string env trm))
       subs)

(* Is there an assumption or substitution about the term? *)
let has_assumption_or_substitution (l : (int * 'a) list) (trm : types) : bool =
  match kind trm with
  | Rel i -> List.mem_assoc i l
  | _ -> false

(* Is there an assumption about the term? *)
let has_assumption (assums : equal_assumptions) (trm : types) : bool =
  has_assumption_or_substitution assums trm

(* Is there a substitution from the provided term? *)
let has_substitution (subs : param_substitutions) (trm : types) : bool =
  has_assumption_or_substitution subs trm

(* Get the assumption about the term *)
let get_assumption (assums : equal_assumptions) (trm : types) : types =
  mkRel (List.assoc (destRel trm) assums)

(* Get the substitution for a parameter *)
let get_substitution (subs : param_substitutions) (trm : types) : types =
  List.assoc (destRel trm) subs

(* Get the terms with no assumptions in the source env *)
let indexes_with_no_assumptions (assums : equal_assumptions) (env : env) : int list =
  let all_is = all_rel_indexes env in
  List.filter (fun i -> not (List.mem_assoc i assums)) all_is

(* Get the number of assumptions *)
let num_assumptions (assums : equal_assumptions) : int =
  List.length assums

(* Assume equality of all terms not in the assumptions of the source env
   TODO this is confusing, clarify what it does *)
let complement_assumptions (assums : equal_assumptions) (env : env) : equal_assumptions =
  let new_is = indexes_with_no_assumptions assums env in
  List.map (fun i -> (i, i)) new_is

(* Split assumptions into the original and its complement *)
let split_assumptions (assums : equal_assumptions) (env : env) : (equal_assumptions * equal_assumptions) =
  (assums, complement_assumptions assums env)

(* Take the union of two sets of assumptions *)
let union_assumptions (assums1 : equal_assumptions) (assums2 : equal_assumptions) : equal_assumptions =
  List.append assums1 assums2

(* Reverse assumptions *)
let reverse_assumptions (assums : equal_assumptions) : equal_assumptions =
  List.map (fun (i, j) -> (j, i)) assums

(* --- DeBruijn operations for assumptions --- *)

(* Unshift all assumptions by an amount *)
let unshift_assumptions_by (n : int) (assums : equal_assumptions) : equal_assumptions =
  List.map (fun (i, j) -> (unshift_i_by n i, unshift_i_by n j)) assums

(* Unshift all substitutions by an amount *)
let unshift_substitutions_by (n : int) (subs : param_substitutions) : param_substitutions =
  List.map (fun (i, t) -> (unshift_i_by n i, unshift_by n t)) subs

(* Shift all assumptions by an amount *)
let shift_assumptions_by (n : int) (assums : equal_assumptions) : equal_assumptions =
  unshift_assumptions_by (- n) assums

(* Shift all substitutions by an amount *)
let shift_substitutions_by (n : int) (subs : param_substitutions) : param_substitutions =
  unshift_substitutions_by (- n) subs

(* Hack *)
let shift_substitutions_by_uncoditional (n : int) (subs : param_substitutions) : param_substitutions =
  List.map (fun (i, t) -> (shift_i_by n i, shift_by_unconditional n t)) subs

(* Unshift all assumption sources by an amount *)
let unshift_from_assumptions_by (n : int) (assums : equal_assumptions) : equal_assumptions =
  List.map (fun (i, j) -> (unshift_i_by n i, j)) assums

(* Unshift all substitution sources by an amount *)
let unshift_from_substitutions_by (n : int) (subs : param_substitutions) : param_substitutions =
  List.map (fun (i, j) -> (unshift_i_by n i, j)) subs

(* Shift all assumption sources by an amount *)
let shift_from_assumptions_by (n : int) (assums : equal_assumptions) : equal_assumptions =
  unshift_from_assumptions_by (- n) assums

(* Shift all substitution sources by an amount *)
let shift_from_substitutions_by (n : int) (subs : param_substitutions) : param_substitutions =
  unshift_from_substitutions_by (- n) subs

(* Unshift all assumption destinations by an amount *)
let unshift_to_assumptions_by (n : int) (assums : equal_assumptions) : equal_assumptions =
  List.map (fun (i, j) -> (i, unshift_i_by n j)) assums

(* Unshift all substitution destinations by an amount *)
let unshift_to_substitutions_by (n : int) (subs : param_substitutions) : param_substitutions =
  List.map (fun (i, j) -> (i, unshift_by n j)) subs

(* Shift all assumption destinations by an amount *)
let shift_to_assumptions_by (n : int) (assums : equal_assumptions) : equal_assumptions =
  unshift_to_assumptions_by (- n) assums

(* Shift all substitution destinations by an amount *)
let shift_to_substitutions_by (n : int) (subs : param_substitutions) : param_substitutions =
  unshift_to_substitutions_by (- n) subs

(* Unshift all assumptions *)
let unshift_assumptions (assums : equal_assumptions) : equal_assumptions =
  unshift_assumptions_by 1 assums

(* Shift all assumptions *)
let shift_assumptions (assums : equal_assumptions) : equal_assumptions =
  shift_assumptions_by 1 assums

(* Shift all substitutions *)
let shift_substitutions (subs : param_substitutions) : param_substitutions =
  shift_substitutions_by 1 subs

(* Unshift all assumption sources *)
let unshift_from_assumptions (assums : equal_assumptions) : equal_assumptions =
  unshift_from_assumptions_by 1 assums

(* Shift all assumption sources *)
let shift_from_assumptions (assums : equal_assumptions) : equal_assumptions =
  shift_from_assumptions_by 1 assums

(* Unshift all assumption destinations *)
let unshift_to_assumptions (assums : equal_assumptions) : equal_assumptions =
  unshift_to_assumptions_by 1 assums

(* Shift all assumption destinations *)
let shift_to_assumptions (assums : equal_assumptions) : equal_assumptions =
  shift_to_assumptions_by 1 assums

(* --- Making new assumptions --- *)

(* Assume that the closest local bindings are equal in both environments *)
let assume_local_n_equal (n : int) (assums : equal_assumptions) : equal_assumptions =
  let new_assums = List.map (fun i -> (i, i)) (range 1 (n + 1)) in
  List.append new_assums (shift_assumptions_by n assums)

(*
 * Build substitutions for the n closest local bindings to dsts
 *)
let build_n_substitutions (n : int) (dsts : types list) (subs : param_substitutions) : param_substitutions =
  let new_subs = List.map2 (fun i t -> (i, t)) (range 1 (n + 1)) dsts in
  List.append new_subs (shift_substitutions_by n subs)

(* Assume that the closest local bindings are equal in both envs *)
let assume_local_equal (assums : equal_assumptions) : equal_assumptions =
  assume_local_n_equal 1 assums

(* Build a substitution for the closest local binding to dst *)
let build_substitution (dst : types) (subs : param_substitutions) : param_substitutions =
  build_n_substitutions 1 [dst] subs

(* --- Applying assumptions --- *)

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
     (fun (s, env) decl ->
       let sub = substitute_params s in
       let decl = CRD.map_constr sub decl in
       (shift_substitutions s, push_rel decl env))
     (unshift_substitutions_by num_rels subs, pop_rel_context num_rels env)
     all_rels)

(* --- Auxiliary functions on swaps --- *)

(*
 * Given a swap map, make a unique swap map (no repeats and only one direction)
 *)
let unique_swaps (swaps : swap_map) : swap_map =
  let same = equal in
  let are_unique (s1, d1) (s2, d2) =
    (same s1 s2 && same d1 d2) || (same s1 d2 && same d1 s2)
  in unique are_unique swaps

(*
 * Filter a swap map by a relation on a pair of types
 *)
let filter_swaps (p : (types * types) -> bool) (swaps : swap_map) : swap_map =
  List.filter p swaps

(*
 * Build a swap map from two arrays of arguments
 *)
let of_arguments (args_o : types array) (args_n : types array) : swap_map =
  Array.to_list (Array.mapi (fun j a -> (a, args_n.(j))) args_o)

(*
 * Build a swap map for all combinations of an array of arguments
 *)
let combinations_of_arguments (args : types array) : swap_map =
  combinations (Array.to_list args)

(*
 * Map a function on two types along a swap map and return a list
 *)
let map_swaps f (s : swap_map) : 'a list =
  List.map f s

(*
 * Flatten a list of swap maps into one swap map with no duplicates
 *)
let merge_swaps (sl : swap_map list) : swap_map =
  unique_swaps (List.flatten sl)

(*
 * Unshift a swap map by n
 *)
let unshift_swaps_by (n : int) (swaps : swap_map) : swap_map =
  List.map (map_tuple (unshift_by n)) swaps

(*
 * Shift a swap map by n
 *)
let shift_swaps_by (n : int) (swaps : swap_map) : swap_map =
  unshift_swaps_by (- n) swaps

(*
 * Unshift a swap map
 *)
let unshift_swaps = unshift_swaps_by 1

(*
 * Shift a swap map
 *)
let shift_swaps = shift_swaps_by 1

(* --- Building and applying swaps --- *)

(*
 * Get a swap map for all combinations of a function application
 *)
let build_swap_map (en : env) (t : types) : swap_map =
  match kind t with
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
    equal
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
    equal
    (map_subterms_env_if_lazy
       (fun _ _ t  -> isApp t)
       (fun en depth t ->
	 let swaps = shift_swaps_by depth swaps in
	 let (f, args) = destApp t in
	 unique
	   equal
	   (apply_swaps_combine (fun s -> mkApp (f, s)) t env args swaps))
       (fun depth -> depth + 1)
       env
       0
       trm)
