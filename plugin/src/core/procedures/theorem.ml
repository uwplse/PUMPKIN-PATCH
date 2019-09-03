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

(* --- TODO for refactoring without breaking things --- *)

(*
 * Infer the type of trm in env
 * Note: This does not yet use good evar map hygeine; will fix that
 * during the refactor.
 *)
let infer_type (env : env) (evd : evar_map) (trm : types) : types =
  let jmt = Typeops.infer env trm in
  j_type jmt

let convertible env sigma t1 t2 = snd (Convertibility.convertible env sigma t1 t2)
let types_convertible env sigma t1 t2 = snd (Convertibility.types_convertible env sigma t1 t2)
               
(* --- End TODO --- *)

(*
 * Zoom all the way into a lambda term
 *
 * TODO common with reversal, factor that out
 *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_rel CRD.(LocalAssum(n, t)) env) b
  | _ ->
     (env, trm)

(*
 * Zoom all the way into a product type
 *)
let rec zoom_product_type (env : env) (typ : types) : env * types =
  match kind typ with
  | Prod (n, t, b) ->
     zoom_product_type (push_rel CRD.(LocalAssum(n, t)) env) b
  | _ ->
     (env, typ)

(*
 * Get the arguments to a function within a term
 * Assumes the function is itself an argument to the term
 * Assumes the function is a constant
 * Dumb for now
 *)
let rec args_to env evd (f : types) (trm : types) : env * (types array) =
  let nonempty (_, a) = Array.length a > 0 in
  match kind trm with
  | Lambda (n, t, b) ->
     args_to (push_rel CRD.(LocalAssum(n,t)) env) evd f b
  | App (g, args) ->
     if convertible env evd g f then
       (env, args)
     else
       let envs_args = List.map (args_to env evd f) (Array.to_list args) in
       if List.exists nonempty envs_args then
	 List.find nonempty envs_args
       else
	 args_to env evd f g
  | LetIn (n, trm, typ, e) ->
     args_to (push_rel CRD.(LocalDef(n, e, typ)) env) evd f e
  | Case (ci, ct, m, bs) ->
     let bs_args = List.map (args_to env evd f) (Array.to_list bs) in
     if List.exists nonempty bs_args then
       List.find nonempty bs_args
     else
       (env, Array.of_list [])
  | Cast (c, k, t) ->
     args_to env evd f c
  | _ -> (* not yet implemented *)
     (env, Array.of_list [])

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
let update_theorem env evd (src : types) (dst : types) (trm : types) : types =
  assert (isConst src && isConst dst);
  let (env, trm) = zoom_lambda_term env trm in
  let _, trm = reduce_term env evd trm in
  let (env_args, args) = args_to env evd src trm in
  let specialize f args = snd (specialize_using specialize_no_reduce env_args f args evd) in
  let src_typ = infer_type env_args evd (specialize src args) in
  let dst_typ = infer_type env_args evd (specialize dst args) in
  let (env_s, src_concl) = zoom_product_type env_args src_typ in
  let (env_d, dst_concl) = zoom_product_type env_args dst_typ in
  let num_hs = nb_rel env in
  let num_src_hs = nb_rel env_s - num_hs in
  let num_dst_hs = nb_rel env_d - num_hs in
  let patch = snd (all_conv_substs env evd (src, dst) trm) in (* TODO evar_map *)
  let patch_dep =
    if num_src_hs = num_dst_hs then
      let patch = shift_by num_src_hs patch in
      unshift_by num_src_hs (snd (all_conv_substs env_s evd (src_concl, dst_concl) patch)) (* TODO evar_map *)
    else
      patch
  in
  let patch_lambda = reconstruct_lambda env patch_dep in
  try
    let _ = infer_type env evd patch_lambda in
    patch_lambda
  with _ ->
    failwith "Patched Theorem is not well-typed"

