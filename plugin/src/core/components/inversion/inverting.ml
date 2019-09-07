(* --- Inversion Component --- *)

open Constr
open Environ
open Evd
open Utilities
open Debruijn
open Reducers
open Substitution
open Assumptions
open Hofs
open Filters
open Factoring
open Reducers
open Contextutils
open Equtils
open Convertibility
open Stateutils
open Envutils
open Inference
       
type inverter = (env * types) -> evar_map -> ((env * types) option) state

(* --- Inverting type paths --- *)

(*
 * Given the factors for a term and an inverter,
 * invert every factor, and produce the inverse factors by reversing it.
 *
 * That is, take [X; X -> Y; Y -> Z] and produce [Z; Z -> Y; Y -> X].
 *
 * If inverting any term along the way fails, produce the empty list.
 *)
let invert_factors (invert : inverter) (fs : factors) =
  let get_all_or_none (l : 'a option list) : 'a list =
    if List.for_all Option.has_some l then
      List.map Option.get l
    else
      []
  in
  bind
    (map_state invert fs)
    (fun inverse_options -> 
      let inverted = List.rev (get_all_or_none inverse_options) in
      match inverted with (* swap final hypothesis *)
      | (env_inv, trm_inv) :: t when List.length t > 0 ->
         let (n, h_inv, _) = destLambda (snd (last t)) in
         let env_inv = push_local (n, h_inv) (pop_rel_context 1 env_inv) in
         ret ((env_inv, trm_inv) :: t)
      | _ ->
         ret inverted)

(* --- Invert a term --- *)

(*
 * Build a swap map of arguments to swap when trying to invert a patch
 *
 * This doesn't handle every type yet, need to generalize
 * When we do, we should test for dependent conclusions or dependent
 * arguments
 * Especially since rels will go negative
 *)
let build_swap_map (env : env) (o : types) (n : types) =
  let rec build_swaps i swap : evar_map -> swap_map state =
    match map_tuple kind swap with
    | (App (f_s, args_s), App (f_n, args_n)) ->
       let is_swap s = ret (not (fold_tuple equal s)) in
       bind
         (filter_swaps is_swap (of_arguments args_s args_n))
         (fun arg_swaps ->
           let swaps_hd = unshift_swaps_by i arg_swaps in
           bind
             (map_swaps (build_swaps i) swaps_hd)
             (fun swaps_tl ->
               ret (merge_swaps (swaps_hd :: swaps_tl))))
    | (Lambda (n_s, t_s, b_s), Lambda (_, t_n, b_n)) ->
       bind
         (build_swaps i (t_s, t_n))
         (fun t_swaps ->
           bind
             (build_swaps (i + 1) (b_s, b_n))
             (fun b_swaps ->
               ret (merge_swaps (t_swaps :: [b_swaps]))))
    | (_, _) ->
       ret no_swaps
  in
  bind
    (bind
       (all_typ_swaps_combs env n)
       (filter_state (fun n sigma -> convertible env sigma o n)))
    (fun srcs ->
      bind
        (map_state (fun s -> build_swaps 0 (s, n)) srcs)
        (fun swaps -> ret (merge_swaps swaps)))

(*
 * Before swapping arguments, try exploiting symmetry of a type like equality
 * For now handles only equality, but can handle other types when we generate
 * their symmetry proofs (using logic similar to the above) and figure out
 * how they fit into their induction principles.
 *
 * Generalizing how to swap arguments is hard and will still probably involve
 * swaps above.
 *)
let exploit_type_symmetry (env : env) (trm : types) sigma =
  map_subterms_env_if_lazy
    (fun _ sigma _ t -> sigma, isApp t && is_rewrite (fst (destApp t)))
    (fun en sigma _ t ->
      let (f, args) = destApp t in
      let i_eq = Array.length args - 1 in
      let eq = args.(i_eq) in
      let sigma, eq_type = infer_type en sigma eq in
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
      in sigma, [mkApp (f, args_r)])
    id
    env
    sigma
    ()
    trm

(*
 * Same as above, but filter to the goal type
 *)
let exploit_type_symmetry_goal env trm goal_type  =
  bind
    (exploit_type_symmetry env trm)
    (fun flipped sigma -> filter_by_type goal_type env sigma flipped)

(*
 * Apply a swap map, and then filter to the goal type
 *)
let apply_swaps_goal env trm goal_type swap_map =
  bind
    (all_conv_swaps_combs env swap_map trm)
    (fun swapped sigma -> filter_by_type goal_type env sigma swapped)
    
(*
 * Try to exploit symmetry and invert a single factor (like a single
 * rewrite) so that it goes from old -> new instead of new -> old.
 *
 * The current algorithm is as follows:
 * 1. If the term is the assumption, return the assumption
 * 2. Merge the environments and substitute the assumptions
 * 3. Get the goal type for the inverted term
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
 * since the inverse patch might show up as a subterm. That is difficult
 * and will increase candidates significantly, so for now we leave it
 * as a separate step.
 *)
let invert_factor (env, rp) =
  bind
    (fun sigma -> reduce_term env sigma rp)
    (fun rp sigma ->
      match kind rp with
      | Lambda (n, old_goal_type, body) ->
         let env_body = push_local (n, old_goal_type) env in
         let sigma, body_type = reduce_type env_body sigma body in
         let new_goal_type = unshift body_type in
         let sigma, rp_goal = all_conv_substs env sigma (old_goal_type, new_goal_type) rp in
         let goal_type = mkProd (n, new_goal_type, shift old_goal_type) in
         bind
           (exploit_type_symmetry_goal env rp_goal goal_type)
           (fun flipped_wt ->
             if List.length flipped_wt > 0 then
               ret (Some (env, List.hd flipped_wt))
             else
               bind
                 (bind
                    (build_swap_map env old_goal_type new_goal_type)
                    (apply_swaps_goal env rp_goal goal_type))
                 (fun swapped_wt ->
                   if List.length swapped_wt > 0 then
	             ret (Some (env, List.hd swapped_wt))
                   else
	             ret None))
           sigma
      | _ ->
         sigma, (Some (env, rp)))

(*
 * Invert a term in an environment
 * Recursively invert function composition
 * Use the supplied inverter to handle factors
 *)
let invert_using (invert : inverter) env (trm : types) =
  bind
    (bind (factor_term env trm) (invert_factors invert))
    (fun inv_fs ->
      if List.length inv_fs > 0 then
        bind (apply_factors inv_fs) (fun app -> ret (Some app))
      else
        ret None)

(*
 * Try to invert a list of terms in an environment
 * Recursively invert function composition
 * Use the supplied inverter to handle low-level inverses
 *)
let invert_terms invert env (ps : types list) =
  bind
    (map_state (invert_using invert env) ps)
    (fun inverted_opts ->
      ret (List.map Option.get (List.filter Option.has_some inverted_opts)))
