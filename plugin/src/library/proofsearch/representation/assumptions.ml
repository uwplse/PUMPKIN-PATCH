(* Equality assumptions for substitutions in proof search *)

open Term
open Environ
open Collections
open Coqenvs
open Debruijn
open Printing

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
  match kind_of_term trm with
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

(* --- Auxiliary functions on swaps --- *)

(*
 * Given a swap map, make a unique swap map (no repeats and only one direction)
 *)
let unique_swaps (swaps : swap_map) : swap_map =
  let same = eq_constr in
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
