(* Strategies for reducing terms *)

open Environ
open Term
open Hofs
open Coqterms
open Utilities
open Debruijn

module CRD = Context.Rel.Declaration

type reducer = env -> types -> types

(* --- Top-level --- *)

let reduce_all (r : reducer) env (trms : types list) : types list =
  List.map (r env) trms

(* --- Combinators and converters --- *)

let chain_reduce (r1 : reducer) (r2 : reducer) env trm : types =
  r2 env (r1 env trm)

let try_reduce (r : reducer) (env : env) (trm : types) : types =
  try r env trm with _ -> trm

(*
 * Reduce the body of a term using the supplied reducer if
 * the predicate p is true on the body. If the term is a function,
 * then this recurses into the body and checks the condition, and so on.
 * It reduces as soon as the condition holds.
 *)
let rec reduce_body_if p (r : reducer) env trm =
  if p env trm then
    r env trm
  else
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       reduce_body_if p r (push_rel CRD.(LocalAssum(n, t)) env) b
    | _ ->
       failwith "Could not specialize"

(* --- Defaults --- *)

(* Default reducer *)
let reduce_term (env : env) (trm : types) : types =
  Reductionops.nf_betaiotazeta Evd.empty trm

(* --- Custom reducers --- *)

(* Don't reduce *)
let do_not_reduce (env : env) (trm : types) : types =
  trm

(* Remove all applications of the identity function *)
let remove_identities (env : env) (trm : types) : types =
  map_term_if
    (fun _ t -> applies_identity t)
    (fun _ t ->
      match kind_of_term t with
      | App (_, args) ->
         Array.get args 1
      | _ ->
         t)
    id
    ()
    trm

(* Remove all applications of the identity function, then default reduce *)
let reduce_remove_identities : reducer =
  chain_reduce remove_identities reduce_term

(* Reduce and also unfold definitions *)
let reduce_unfold (env : env) (trm : types) : types =
  Reductionops.nf_all env Evd.empty trm

(* Reduce and also unfold definitions, but weak head *)
let reduce_unfold_whd (env : env) (trm : types) : types =
  Reductionops.whd_all env Evd.empty trm

(* Weak-head reduce a term if it is a let-in *)
let reduce_whd_if_let_in (env : env) (trm : types) : types  =
  if isLetIn trm then
    Reduction.whd_betaiotazeta env trm
  else
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
 * more hypotheses to our patch, and then later we remove them.
 * We should fix this eventually.
 *)
let rec remove_unused_hypos (env : env) (trm : types) : types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     let env_b = push_rel CRD.(LocalAssum(n, t)) env in
     let b' = remove_unused_hypos env_b b in
     (try
        let num_rels = nb_rel env in
        let env_ill = push_rel CRD.(LocalAssum (n, mkRel (num_rels + 1))) env in
        let _ = infer_type env_ill b' in
        remove_unused_hypos env (unshift b')
      with _ ->
        mkLambda (n, t, b'))
  | _ ->
     trm
