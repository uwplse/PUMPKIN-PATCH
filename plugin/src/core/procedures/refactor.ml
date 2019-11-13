open Envutils
open Substitution
open Stateutils
open Convertibility
open Inference
open Equtils

(*
 * Refactoring functionality
 *)

(* --- Correctness proofs --- *)

(* 
 * Prove coherence with the components search finds
 * Return the coherence proof term and its type
 *)
let maybe_prove_replace_correct prove_correct env trm sub =
  if prove_correct then
    branch_state
      (fun (trm, sub) sigma -> convertible env sigma trm sub)
      (fun (trm, sub) sigma ->
        let sigma, typ = infer_type env sigma trm in
        let refl = apply_eq_refl { typ; trm } in
        let refl_typ = apply_eq { at_type = typ; trm1 = trm; trm2 = sub} in
        ret (Some (refl, refl_typ)) sigma)
      (fun (trm, sub) ->
        (* not yet implemented *)
        ret None)
      (trm, sub)
  else
    ret None

(* --- Top-level refactoring functions --- *)

(* Replace all subterms convertible with conv_trm in trm *)
let replace_all_convertible prove_correct env conv_trms trm sigma =
  let trm = unwrap_definition env trm in
  let sigma, sub =
    fold_right_state
      (fun conv_trm trm sigma ->
        all_conv_substs env sigma (conv_trm, conv_trm) trm)
      conv_trms
      trm
      sigma
  in
  let sigma, pf = maybe_prove_replace_correct prove_correct env trm sub sigma in
  sigma, (sub, pf)
