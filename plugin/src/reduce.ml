(* Reduction *)

open Environ
open Term
open Hofs
open Coqterms
open Utilities
open Debruijn

type reduction_strategy = env -> types -> types

(* Remove identity terms for reduction, unsafe and only called when applies_identity holds *)
let remove_identity (trm : types) : types =
  match kind_of_term trm with
  | App (_, args) ->
     Array.get args 1
  | _ ->
     trm

(* Remove all identity terms for reduction *)
let remove_identities (trm : types) : types =
  map_term_if
    (fun _ t -> applies_identity t)
    (fun _ t -> remove_identity t)
    id
    ()
    trm

(*
 * This function removes any terms from the hypothesis of a lambda
 * that are not referenced in the body, so that the term
 * has only hypotheses that are referenced.
 *
 * This is a workaround for the way that the procedure for
 * changes in constructor arguments works.
 * Basically, it should return earlier once it finds the
 * goal patch. But right now, the implementation isn't great,
 * so instead we treat it like any other goal patch and add
 * more hypothesis to our patch, and then later we remove them.
 * We should fix this eventually.
 *)
let rec remove_unused_hypos (env : env) (trm : types) : types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     let env_b = push_rel (n, None, t) env in
     let b' = remove_unused_hypos env_b b in
     (try
        let num_rels = nb_rel env in
        let env_ill = push_rel (n, None, mkRel (num_rels + 1)) env in
        let _ = infer_type env_ill b' in
        remove_unused_hypos env (unshift b')
      with _ ->
        mkLambda (n, t, b'))
  | _ ->
     trm

(* Reduce and also unfold definitions *)
let reduce_unfold : reduction_strategy =
  (fun env trm ->
    Reductionops.nf_betadeltaiota env Evd.empty trm)

(* Reduce and also unfold definitions, but weak head *)
let reduce_unfold_hd : reduction_strategy =
  (fun env trm ->
    Reductionops.whd_betadeltaiota env Evd.empty trm)

(* Reduce before applying abstraction, and remove all identity terms *)
let reduce : reduction_strategy =
  (fun env trm ->
    Reduction.nf_betaiota env (remove_identities trm))

(* Try to reduce, but let failure be OK *)
let try_reduce : reduction_strategy =
  (fun env trm -> try reduce env trm with _ -> trm)

(* Do not reduce before applying abstraction, but still remove all identity terms *)
let do_not_reduce : reduction_strategy = (fun _ trm -> remove_identities trm)

(* Reduce candidates using a reduction strategy *)
let reduce_candidates (reducer : reduction_strategy) (env : env) (cs : types list) : types list =
  List.map (reducer env) cs
