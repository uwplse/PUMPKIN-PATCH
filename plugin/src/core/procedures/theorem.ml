(* Updating theorems instead of proofs *)

open Constr
open Environ
open Substitution
open Debruijn
open Reducers
open Specialization
open Evd
open Zooming
open Contextutils
open Inference
open Convertibility
open Envutils
open Zooming
open Stateutils

(*
 * Get the arguments to a function within a term
 * Assumes the function is itself an argument to the term
 * Assumes the function is a constant
 * Dumb for now
 *)
let rec args_to env (f : types) (trm : types) sigma =
  let nonempty (_, a) = Array.length a > 0 in
  match kind trm with
  | Lambda (n, t, b) ->
     args_to (push_local (n, t) env) f b sigma
  | App (g, args) ->
     branch_state
       (fun g sigma -> convertible env sigma g f)
       (fun _ -> ret (env, args))
       (fun g sigma ->
         bind
           (map_state (args_to env f) (Array.to_list args))
           (fun envs_args sigma_args ->
             if List.exists nonempty envs_args then
	       sigma_args, List.find nonempty envs_args
             else
	       args_to env f g sigma)
           sigma)
       g
       sigma
  | LetIn (n, trm, typ, e) ->
     args_to (push_rel CRD.(LocalDef(n, e, typ)) env) f e sigma
  | Case (ci, ct, m, bs) ->
     bind
       (map_state (args_to env f) (Array.to_list bs))
       (fun bs_args sigma_bs ->
         if List.exists nonempty bs_args then
           sigma_bs, List.find nonempty bs_args
         else
           sigma, (env, Array.of_list []))
       sigma
  | Cast (c, k, t) ->
     args_to env f c sigma
  | _ -> (* not yet implemented *)
     sigma, (env, Array.of_list [])

(*
 * Subtitute a term into a simple theorem
 * Try to update dependent types appropriately
 *
 * For now, operates at two levels, so gets the argument where the
 * type is applied.
 * When we add path-finding to this, we can omit this part.
 *
 * Also assumes src, dst constants, which saves us from shifting for now.
 * This is probably fine since they should be theorem names.
 * And doesn't do anything fancy yet like actually look at the terms.
 * It's a pretty naive heuristic to get this started.
 *)
let update_theorem env (src : types) (dst : types) (trm : types) sigma =
  assert (isConst src && isConst dst);
  let (env, trm) = zoom_lambda_term env trm in
  let sigma, trm = reduce_term env sigma trm in
  let sigma, (env_args, args) = args_to env src trm sigma in
  let specialize f args = specialize_using specialize_no_reduce env_args f args in
  let sigma, src_typ = bind (specialize src args) (fun t sigma -> infer_type env_args sigma t) sigma in
  let sigma, dst_typ = bind (specialize dst args) (fun t sigma -> infer_type env_args sigma t) sigma in
  let (env_s, src_concl) = zoom_product_type env_args src_typ in
  let (env_d, dst_concl) = zoom_product_type env_args dst_typ in
  let num_hs = nb_rel env in
  let num_src_hs = nb_rel env_s - num_hs in
  let num_dst_hs = nb_rel env_d - num_hs in
  let sigma, patch = all_conv_substs env sigma (src, dst) trm in (* TODO evar_map *)
  let sigma, patch_dep =
    if num_src_hs = num_dst_hs then
      let patch = shift_by num_src_hs patch in
      let sigma, subbed = all_conv_substs env_s sigma (src_concl, dst_concl) patch in
      sigma, unshift_by num_src_hs subbed
    else
      sigma, patch
  in
  let patch_lambda = reconstruct_lambda env patch_dep in
  try
    let sigma, _ = infer_type env sigma patch_lambda in
    sigma, patch_lambda
  with _ ->
    failwith "Patched Theorem is not well-typed"

