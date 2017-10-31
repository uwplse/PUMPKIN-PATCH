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

type inverter = (env * types) -> (env * types) option
type factors = (env * types) list

(* --- Auxiliary functions --- *)

let filter_non_empty (la : 'a list list) : 'a list list =
  List.filter (fun l -> List.length l > 0) la

(* --- Zooming and focusing --- *)

(*
 * Zoom all the way into a lambda term
 *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_rel (n, None, t) env) b
  | _ ->
     (env, trm)

let assumption : types = mkRel 1

(*
 * Apply the assumption (last term in the environment) in the term
 *)
let focus (fs : factors) (trm : types) : types =
  if List.length fs > 0 then
    assumption
  else
    trm

(*
 * Check if the term is the assumption (last term in the environment)
 *)
let is_assumption (env : env) (trm : types) : bool =
  convertible env trm assumption

(*
 * Assume a term of type typ in an environment
 *)
let assume (env : env) (n : name) (typ : types) : env =
  let env_pop = pop_rel_context 1 env in
  push_rel (n, None, typ) env_pop

(* --- Find paths --- *)

(*
 * Auxiliary path-finding function, once we are zoomed into a lambda
 * and the hypothesis we care about is the assumption (first term
 * in the environment).
 *
 * The type path is in reverse order for efficiency, and is really
 * a list of environments (assumptions) and terms. When we refer to 
 * "the end" it is the head of the list.
 *
 * The algorithm is as follows:
 * 1. If a term is the assumption, return a single path with 
 *    the environment and term, which is the identity path.
 * 2. Otherwise, if it is an application:
 *    a. Recursively get the type path for each argument.
 *    b. If there are multiple nonempty type paths, then we cannot abstract out
 *       the assumption in a single function, so return the identity path.
 *    c. Otherwise, get the only non-empty path, then:
 *       i. Focus in on each argument with the current assumption
 *       ii. Assume the conclusion of the element at the end of the path
 *       ii. Apply the function to the focused arguments in the environment
 *            with the new assumption, and add that to the end of the path
 *       iv. If applying the assumption at any point fails, return the empty
 *           path
 *
 * In other words, this is going as deep into the term as possible and
 * finding some Y for which X -> Y. It is then focusing in assuming Y,
 * and asking if there is some path from Y to the conclusion.
 *
 * It does not yet handle when Y depends on X. I think that case should
 * fail anyways, since that type path shouldn't be invertible.
 *)
let rec find_path (env : env) (trm : types) : factors =
  if is_assumption env trm then
    [(env, trm)]
  else
    match kind_of_term trm with
    | App (f, args) ->
       let paths = Array.map (find_path env) args in
       let nonempty_paths = filter_non_empty (Array.to_list paths) in
       if List.length nonempty_paths > 1 then
	 [(env, trm)]
       else if List.length nonempty_paths = 1 then
	 let path = List.hd nonempty_paths in
	 let (env_arg, arg) = List.hd path in
         let focus_arg i a = focus (Array.get paths i) a in
         let args_focused = Array.mapi focus_arg args in
	 try
           let t = unshift (infer_type env_arg arg) in
	   (assume env Anonymous t, mkApp (f, args_focused)) :: path
	 with _ ->
	   []
       else
	 []
    | _ -> (* other terms not yet implemented *)
       []

(*
 * Given a term trm, if the type of trm is a function type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F)
 *
 * First zoom in all the way, then use the auxiliary path-finding
 * function.
 *)
let factor_term (env : env) (trm : types) : factors =
  let (env_zoomed, trm_zoomed) = zoom_lambda_term env (reduce env trm) in
  let path_body = find_path env_zoomed trm_zoomed in
  List.map
    (fun (env, body) ->
      if is_assumption env body then
	(env, body)
      else
	let (n, _, t) = lookup_rel 1 env in
	(pop_rel_context 1 env, mkLambda (n, t, body)))
    path_body

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
 * Swap the final hypothesis in an inverted type path so that
 * it has the type of the old conclusion instead of the old assumption
 *)
let invert_final_hypothesis (fs : factors) : factors =
  match fs with
  | (env_inv, trm_inv) :: t when List.length t > 0 ->
     let (n, h_inv, _) = destLambda (snd (last t)) in
     (assume env_inv n h_inv, trm_inv) :: t
  | _ ->
     fs

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
    match inverted with (* swap final hypothesis *) (* TODO merge with above *)
    | (env_inv, trm_inv) :: t when List.length t > 0 ->
       let (env_inv', trm_inv') = last t in
       let (n, h_inv, _) = destLambda trm_inv' in
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
  if is_assumption env rp then
    Some (env, rp)
  else
    let rp = reduce env rp in
    let (n, old_goal_type, body) = destLambda rp in
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
