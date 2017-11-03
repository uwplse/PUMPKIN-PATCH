(* Filters *)

open Term
open Environ
open Coqterms
open Debruijn

type 'a filter_strategy = env -> types -> 'a list -> 'a list

(* Filter trms to those that have type typ in env *)
let filter_by_type (env : env) (typ : types) (trms : types list) : types list =
  try
    List.filter (has_type env typ) trms
  with
  | _ -> []

(* Find the singleton list with the first term that has type typ *)
let find_by_type (env : env) (typ : types) (trms : types list) : types list =
  try
    [List.find (has_type env typ) trms]
  with
  | _ -> []

(* Filter etrms to those that are unifiable with a term of type typ *)
let filter_unifiable (env : env) (typ : types) (etrms : eterm list) : eterm list =
  let unified = List.map (fun (evm, trm) -> (unifiable env typ (evm, trm), trm)) etrms in
  List.map
    (fun (evmo, trm) -> (Option.get evmo, trm))
    (List.filter (fun (evmo, trm) -> Option.has_some evmo) unified)

(* Filter a list of terms to those not exactly the same as the supplied term *)
let filter_not_same (_ : env) (trm : types) (trms : types list) : types list =
  let same = eq_constr trm in (* exact equality for constructors *)
  List.filter (fun t -> not (same t)) trms

(*
 * Eliminate inductive hypotheses if possible.
 * This takes in a list of reduced candidates and filters out
 * the ones that still reference the IH.
 *
 * For now, only deals with candidates that refer explicitly to IH.
 * The ones that do will not pass the filter,
 * while the ones that don't will, and will then be type-checked.
 *
 * Sometimes this will not be possible, in which case we need a backup plan.
 * This is not yet implemented.
 *)
let filter_ihs (env : env) (cs : types list) : types list =
  let env_no_ih = pop_rel_context 1 env in
  List.filter
    (fun c ->
      let c_no_ih = unshift c in
      try
        let c_type = infer_type env_no_ih c_no_ih in
        true
      with _ -> false)
    cs