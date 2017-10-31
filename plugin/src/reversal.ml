(* Functions for inverting symmetric patches *)

open Term
open Environ
open Coqterms
open Collections
open Printing
open Utilities
open Debruijn
open Reduce
open Substitution
open Assumptions
open Hofs
open Filters
open Coqterms
open Names
open Factoring

type inverter = (env * types) -> (env * types) option

(* --- Auxiliary functions --- *)

(*
 * Apply a type path to reconstruct a single term
 *)
let apply_type_path (fs : factors) : types =
  let (env, base) = List.hd fs in
  let body =
    List.fold_right
      (fun (_, t) t_app ->
	mkApp (shift t, Array.make 1 t_app))
      (List.tl fs)
      base
  in reduce env (reconstruct_lambda env body)

(* --- Inverting type paths --- *)

(*
 * Given a type path for a term and an inverter,
 * invert every term in the type path, and produce the inverse type path
 * by reversing it.
 *
 * That is, take [X; X -> Y; Y -> Z] and produce [Z; Z -> Y; Y -> X].
 *
 * If inverting any term along the way fails, produce the empty path.
 *)
let invert_type_path (invert : inverter) (fs : factors) : factors =
  let inverse_options = List.map invert fs in
  if List.for_all Option.has_some inverse_options then
    let inverted = List.rev (List.map Option.get inverse_options) in
    match inverted with (* swap final hypothesis *)
    | (env_inv, trm_inv) :: t when List.length t > 0 ->
       let (n, h_inv, _) = destLambda (snd (last t)) in
       let env_inv = push_rel (n, None, h_inv) (pop_rel_context 1 env_inv) in
       (env_inv, trm_inv) :: t
    | _ ->
       inverted
  else
    []

(* --- Invert a term --- *)

(*
 * Build a swap map of arguments to swap when trying to reverse a patch
 *
 * This doesn't handle every type yet, need to generalize
 * When we do, we should test for dependent conclusions or dependent
 * arguments
 * Especially since rels will go negative
 *)
let build_swap_map (env : env) (o : types) (n : types) : swap_map =
  let rec build_swaps i swap =
    match map_tuple kind_of_term swap with
    | (App (f_s, args_s), App (f_n, args_n)) ->
       let is_swap s = not (fold_tuple eq_constr s) in
       let arg_swaps = filter_swaps is_swap (of_arguments args_s args_n) in
       let swaps = unshift_swaps_by i arg_swaps in
       merge_swaps (swaps :: (map_swaps (build_swaps i) swaps))
    | (Lambda (n_s, t_s, b_s), Lambda (_, t_n, b_n)) ->
       let t_swaps = build_swaps i (t_s, t_n) in
       let b_swaps = build_swaps (i + 1) (b_s, b_n) in
       merge_swaps (t_swaps :: [b_swaps])
    | (_, _) ->
       no_swaps
  in
  let srcs = List.filter (convertible env o) (all_typ_swaps_combs env n) in
  merge_swaps (List.map (fun s -> build_swaps 0 (s, n)) srcs)

(*
 * Before swapping arguments, try exploiting symmetry of a type like equality
 * For now handles only equality, but can handle other types when we generate
 * their symmetry proofs (using logic similar to the above) and figure out
 * how they fit into their induction principles.
 *
 * Generalizing how to swap arguments is hard and will still probably involve
 * swaps above.
 *)
let rec exploit_type_symmetry (env : env) (trm : types) : types list =
  map_subterms_env_if_lazy
    (fun _ _ t -> isApp t && is_rewrite (fst (destApp t)))
    (fun en _ t ->
      let (f, args) = destApp t in
      let i_eq = Array.length args - 1 in
      let eq = args.(i_eq) in
      let eq_type = infer_type en eq in
      let eq_args = List.append (Array.to_list (snd (destApp eq_type))) [eq] in
      let eq_r = mkApp (eq_sym, Array.of_list eq_args) in
      let i_src = 1 in
      let i_dst = 4 in
      let args_r =
	Array.mapi
	  (fun i a ->
	    if i = i_eq then
	      eq_r
	    else if i = i_src then
	      args.(i_dst)
	    else if i = i_dst then
	      args.(i_src)
	    else
	      a)
	  args
      in [mkApp (f, args_r)])
    id
    env
    ()
    trm

(*
 * Try to exploit symmetry and reverse a simple patch, (like a single
 * rewrite) so that it goes from old -> new instead of new -> old.
 *
 * The current algorithm is as follows:
 * 1. If the term is the assumption, return the assumption
 * 2. Merge the environments and substitute the assumptions
 * 3. Get the goal type for the reversal
 * 4. Try exploiting symmetry like eq_ind and eq_ind_r
 * 5. If that fails:
 *    a) See if we can swap some arguments in new_goal_type to get old_goal_type
 *    b) If we can, then track those substitutions.
 *    c) Swap the goal types, since that must happen.
 *    d) Swap the tracked substitutions, which encompass dependencies.
 *    e) Filter that list for candidates that have the goal type.
 *
 * There is likely work to get
 * the swap map calculation to generalize. We need lots of benchmarks to test
 * this, and may want to fall back to the old algorithm when we fail.
 * If we fall back to swapping terms, for example, we may also want to
 * swap upward (if we would swap two types' terms, then also swap those terms).
 *
 * Finally, we may want to move this up to the search process itself,
 * since the reverse patch might show up as a subterm. That is difficult
 * and will increase candidates significantly, so for now we leave it
 * as a separate step.
 *)
let invert_patch (env, rp) : (env * types) option =
  let rp = reduce env rp in
  match kind_of_term rp with
  | Lambda (n, old_goal_type, body) ->
     let env_body = push_rel (n, None, old_goal_type) env in
     let new_goal_type = unshift (reduce env_body (infer_type env_body body)) in
     let rp_goal = all_conv_substs env (old_goal_type, new_goal_type) rp in
     let goal_type = mkProd (n, new_goal_type, shift old_goal_type) in
     let flipped = exploit_type_symmetry env rp_goal in
     let flipped_wt = filter_by_type env goal_type flipped in
     if List.length flipped_wt > 0 then
       Some (env, List.hd flipped_wt)
     else
       let swap_map = build_swap_map env old_goal_type new_goal_type in
       let swapped = all_conv_swaps_combs env swap_map rp_goal in
       let swapped_wt = filter_by_type env goal_type swapped in
       if List.length swapped_wt > 0 then
	 Some (env, List.hd swapped_wt)
       else
	 None
  | _ ->
     Some (env, rp)

(*
 * Invert a term in an environment
 * Recursively invert function composition
 * Use the supplied inverter to handle low-level inverses
 *)
let invert_using (invert : inverter) (env : env) (trm : types) : types option =
  let fs = factor_term env trm in
  let inv_path = invert_type_path invert fs in
  if List.length inv_path > 0 then
    Some (apply_type_path inv_path)
  else
    None

(*
 * Try to invert a list of terms in an environment
 * Recursively invert function composition
 * Use the supplied inverter to handle low-level inverses
 *)
let invert_patches invert (env : env) (ps : types list) : types list =
  List.map
    Option.get
    (List.filter Option.has_some (List.map (invert_using invert env) ps))
