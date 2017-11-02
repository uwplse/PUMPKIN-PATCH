(* --- The Factoring Component --- *)

open Term
open Environ
open Coqterms
open Specialization
open Names
open Collections
open Debruijn

type factors = (env * types) list

(* --- Assumptions for path finding --- *)

let assumption : types = mkRel 1

(*
 * Apply the assumption (last term in the environment) in the term
 *)
let apply_assumption (fs : factors) (trm : types) : types =
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

(* --- Path-finding auxiliary functionality --- *)

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
 *       i. Zoom in on each argument with the current assumption
 *       ii. Assume the conclusion of the element at the end of the path
 *       ii. Apply the function to the zoomed arguments in the environment
 *            with the new assumption, and add that to the end of the path
 *       iv. If applying the assumption at any point fails, return the empty
 *           path
 *
 * In other words, this is going as deep into the term as possible and
 * finding some Y for which X -> Y. It is then assuming Y,
 * and asking if there is some path from Y to the conclusion.
 *
 * It does not yet handle when Y depends on X. That case should
 * fail for inveresion, but we might want it if we use factoring for other
 * purposes, like to simplify abstraction.
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
         let assume_arg i a = apply_assumption (Array.get paths i) a in
         let args_assumed = Array.mapi assume_arg args in
	 try
           let t = unshift (infer_type env_arg arg) in
	   (assume env Anonymous t, mkApp (f, args_assumed)) :: path
	 with _ ->
	   []
       else
	 []
    | _ -> (* other terms not yet implemented *)
       []

(* --- Top-level factoring --- *)

(*
 * Given a term trm, if the type of trm is a function type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F)
 *
 * First zoom in all the way, then use the auxiliary path-finding
 * function.
 *)
let factor_term (env : env) (trm : types) : factors =
  let r = reduce_using reduce_term in
  let (env_zoomed, trm_zoomed) = zoom_lambda_term env (r env trm) in
  let path_body = find_path env_zoomed trm_zoomed in
  List.map
    (fun (env, body) ->
      if is_assumption env body then
	(env, body)
      else
	let (n, _, t) = lookup_rel 1 env in
	(pop_rel_context 1 env, mkLambda (n, t, body)))
    path_body

(* --- Using factors --- *)

(*
 * Reconstruct factors as terms using hypotheses from the environment.
 *
 * This basically produces a friendly external form in the correct order,
 * and using functions instead of closures. Inversion doesn't use this
 * for efficiency, but top-level functions probably want to.
 *)
let reconstruct_factors (fs : factors) : types list =
  List.map
    (fun (en, t) -> reconstruct_lambda en t)
    (List.tl (List.rev fs))

(* Apply factors to reconstruct a single term *)
let apply_factors (fs : factors) : types =
  let (env, base) = List.hd fs in
  let body =
    List.fold_right
      (fun (en, t) t_app ->
        specialize_using specialize_no_reduce en (shift t) (Array.make 1 t_app))
      (List.tl fs)
      base
  in reduce_using reduce_term env (reconstruct_lambda env body)
