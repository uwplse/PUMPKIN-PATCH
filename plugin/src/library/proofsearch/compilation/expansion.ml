(* Expanding proof categories *)

open Names
open Environ
open Term
open Coqterms
open Coqenvs
open Proofcat
open Proofcatterms
open Evaluation
open Collections
open Utilities
open Debruijn
open Printing

(* --- Type definitions --- *)

type 'a expansion_strategy = 'a -> 'a

(* --- Terms and types --- *)

(* Expand a product type exactly once *)
let expand_product (env : env) ((n, t, b) : Name.t * types * types) : proof_cat =
  let t' = eval_theorem env t in
  let env' = push_rel (n, None, t) env in
  let b' = eval_theorem env' b in
  let c = substitute_categories t' b' in
  bind c (initial c, LazyBinding (mkRel 1, env'), terminal t')

(* Expand a lambda term exactly once *)
let expand_lambda (env : env) ((n, t, b) : Name.t * types * types) : proof_cat =
  expand_product env (n, t, b)

(*
 * Expand an inductive type
 * This is unfinished, and currently unused for any benchmarks
*)
let expand_inductive (env : env) (((i, ii), u) : pinductive) : proof_cat =
  let mbody = lookup_mutind_body i env in
  check_inductive_supported mbody;
  let bodies = mbody.mind_packets in
  let env_ind = push_rel_context (bindings_for_inductive env mbody (Array.to_list bodies)) env in
  let body = bodies.(ii) in
  let constrs =
    List.map
      (fun ci -> mkConstructU (((i, ii), ci), u))
      (from_one_to (Array.length body.mind_consnames))
  in
  let cs = List.map (eval_proof env_ind) constrs in
  List.fold_left
    (fun cind c ->
      let os = (terminal c) :: (objects cind) in
      let ms = List.append (morphisms c) (morphisms cind) in
      make_category os ms (initial_opt cind) None)
    (List.hd cs)
    (List.tl cs)

(*
 * Expand application exactly once
 * Assumes there is at least one argument
 *)
let expand_app (env : env) ((f, args) : types * types array) =
  assert (Array.length args > 0);
  let arg = args.(0) in
  let f' = eval_proof env (mkApp (f, singleton_array arg)) in
  let arg' = substitute_categories (eval_proof env arg) f' in
  bind_apply_function (LazyBinding (f, env)) 1 arg'

(* --- Contexts --- *)

(*
 * Expand a term exactly once
 * Default to using f when it cannot be expanded further
 * Error if the type context doesn't hold any terms
 *)
let expand_term (default : env -> types -> proof_cat) (o : context_object) : proof_cat =
  let (trm, env) = dest_context_term o in
  match kind_of_term trm with
  | Prod (n, t, b) ->
      expand_product env (n, t, b)
  | Lambda (n, t, b) ->
      expand_lambda env (n, t, b)
  | Ind ((i, ii), u) ->
      expand_inductive env ((i, ii), u)
  | App (f, args) ->
     (match kind_of_term f with
     | Lambda (n, t, b) ->
        (* Does not yet delta-reduce *)
        if Array.length args > 0 then
          expand_app env (f, args)
        else
          default env trm
     | _ ->
        default env trm)
  | _ ->
      default env trm

(* Expand a product type as far as its conclusion goes *)
let expand_product_fully (o : context_object) : proof_cat =
  let rec expand_fully env (n, t, b) =
    match kind_of_term b with
    | Prod (n', t', b') ->
       let t'' = eval_theorem env t in
       let env' = push_rel (n, None, t) env in
       let b'' = expand_fully env' (n', t', b') in
       let c = substitute_categories t'' b'' in
       bind c (initial c, LazyBinding (mkRel 1, env'), terminal t'')
    | _ ->
       expand_product env (n, t, b)
  in expand_fully (context_env o) (destProd (fst (dest_context_term o)))

(* --- Categories --- *)

(*
 * Expand the terminal object of c exactly once
 * Return c if it cannot be expanded
 *)
let expand_terminal (c : proof_cat) : proof_cat =
  let t = terminal c in
  match t with
  | Context (Term (trm, env), i) ->
     let ms = morphisms c in
     let concls = arrows_with_dest t ms in
     let binding =
       if non_empty concls then
         let (_, ext, _) = List.hd concls in (* arbitrary for now *)
         ext
       else
         AnonymousBinding
     in
     let exp = expand_term (eval_theorem_bind binding) t in
     substitute_terminal c exp
  | _ ->
      c

(*
 * Utility function for expanding inductive proofs
 * Partition the morphisms of a category into two parts:
 * 1. Morphisms that end in a product type that is not an assumption
 * 2. Morphisms that do not
 *)
let partition_expandable (c : proof_cat) : (arrow list * arrow list) =
  List.partition
    (map_dest (and_p context_is_product (is_not_assumption c)))
    (morphisms c)

(*
 * Utility function for expanding inductive proofs
 * Expand conclusions of different cases of an inductive proof that are dependent
 *)
let expand_inductive_conclusions (ms : arrow list) : proof_cat list =
  List.map
    (fun (s, e, d) ->
      let dc = expand_product_fully d in
      let map_i_to_src = map_if (objects_equal (initial dc)) (always s) id in
      let arity = (List.length (morphisms dc)) - 1 in
      bind_apply_function
        (shift_ext_by arity (substitute_ext_env (context_env (terminal dc)) e))
        arity
        (apply_functor map_i_to_src (map_source_arrow map_i_to_src) dc))
    ms

(*
 * Expand all conclusions of an inductive proof fully
 * (Fully expand all product types in conclusions)
 *
 * If there's a bug here, it might be because we need to
 * substitute in an environment with the inductive bindings pushed
 * (see git history prior to July 2nd, 2017). This is
 * especially relevant when we add support for mutually
 * inductive types.
 *)
let expand_inductive_conclusions_fully (c : proof_cat) : proof_cat =
  let c_os = objects c in
  let (ms_to_expand, old_ms) = partition_expandable c in
  let old_os = all_objects_except_those_in (conclusions ms_to_expand) c_os in
  let expanded = expand_inductive_conclusions ms_to_expand in
  let new_os = flat_map (map_objects (all_objects_except_those_in c_os)) expanded in
  let new_ms = flat_map morphisms expanded in
  let os = List.append old_os new_os in
  let ms = List.append old_ms new_ms in
  make_category os ms (initial_opt c) None

(* For an inductive proof, expand n inductive parameters and the principle P *)
let expand_inductive_params (n : int) (c : proof_cat) : proof_cat =
  let rec expand n' c' =
    if n' < 0 || (not (context_is_product (terminal c'))) then
      c'
    else
      expand (n' - 1) (expand_terminal c')
  in expand n c

(* Check if an o is the type of an applied inductive hypothesis in c *)
let applies_ih (en : env) (p : types) (c : proof_cat) : context_object -> bool =
  and_p
    (and_p context_is_app (is_assumption c))
    (fun o ->
      let (f, _) = context_as_app o in
      let offset = shortest_path_length c o in
      has_type en p (unshift_by offset f))

(*
 * Bind the inductive hypotheses in an expanded constructor with parameters
 *
 * Assumes it's an expanded constructor, but doesn't check for structure
 * This also may fail if the IH is applied to something when we expand
 * So we should test for that case
 *)
let bind_ihs (c : proof_cat) : proof_cat =
  let env_with_p = context_env (context_at_index c 1) in
  let (_, _, p) = lookup_rel 1 env_with_p in
  let env = pop_rel_context 1 env_with_p in
  apply_functor
    id
    (map_if
       (map_dest (applies_ih env p c))
       (map_ext_arrow (always (fresh_ih ())))
       id)
    c

(*
 * Expand an inductive constructor
 * That is, expand its conclusion fully if it is dependent
 * Then mark the edges that are inductive hypotheses
 *)
let expand_constr (c : proof_cat) : proof_cat =
  let c_exp = bind_ihs (expand_inductive_conclusions_fully c) in
  let ms = morphisms c_exp in
  let assums = assumptions ms in
  let concls = conclusions ms in
  let tr = List.hd (all_objects_except_those_in assums concls) in (*arbitrary*)
  make_category (objects c_exp) ms (initial_opt c_exp) (Some tr)

