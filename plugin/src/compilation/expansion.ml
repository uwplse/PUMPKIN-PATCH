(* Expanding proof categories *)

open Stateutils
open Names
open Environ
open Evd
open Constr
open Proofcat
open Proofcatterms
open Evaluation
open Utilities
open Debruijn
open Declarations
open Indutils
open Contextutils
open Convertibility
open Envutils
open Inference
open Checking
open Evaluation

(* --- Type definitions --- *)

type 'a expansion_strategy = 'a -> evar_map -> 'a state

(* --- Terms and types --- *)

(* --- Contexts --- *)

(* --- Categories --- *)

(*
 * Utility function for expanding inductive proofs
 * Partition the morphisms of a category into two parts:
 * 1. Morphisms that end in a product type that is not a hypothesis
 * 2. Morphisms that do not
 *)
let partition_expandable (c : proof_cat) =
  partition_state
    (map_dest 
       (fun o ->
	 and_state 
	   (fun o -> ret (context_is_product o)) 
	   (is_not_hypothesis c)
	   o
	   o))
    (morphisms c)

(*
 * Utility function for expanding inductive proofs
 * Expand conclusions of different cases of an inductive proof that are dependent
 *)
let expand_inductive_conclusions (ms : arrow list) =
  map_state
    (fun (s, e, d) ->
      bind
	(expand_product_fully d)
	(fun dc ->
	  let map_i_to_src = 
	    branch_state (objects_equal (initial dc)) (fun _ -> ret s) ret
	  in
	  let arity = (List.length (morphisms dc)) - 1 in
	  let env = substitute_ext_env (context_env (terminal dc)) e in
	  bind
	    (apply_functor map_i_to_src (map_source_arrow map_i_to_src) dc)
	    (bind_apply_function (shift_ext_by arity env) arity)))
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
let expand_inductive_conclusions_fully (c : proof_cat) sigma =
  let sigma, c_os = objects c sigma in
  let sigma, (ms_to_expand, old_ms) = partition_expandable c sigma in
  let sigma, old_os = all_objects_except_those_in (conclusions ms_to_expand) c_os sigma in
  let sigma, expanded = expand_inductive_conclusions ms_to_expand sigma in
  let sigma, new_os = flat_map_state (map_objects (all_objects_except_those_in c_os)) expanded sigma in
  let new_ms = flat_map morphisms expanded in
  let os = List.append old_os new_os in
  let ms = List.append old_ms new_ms in
  make_category os ms (initial_opt c) None sigma

(* Check if an o is the type of an applied inductive hypothesis in c *)
let applies_ih (env : env) (p : types) (c : proof_cat) (o : context_object) =
  if context_is_app o then
    let (f, _) = context_as_app o in
    bind
      (shortest_path_length c o)
      (fun n ->
	and_state 
	  (is_hypothesis c) 
	  (fun f sigma -> has_type env sigma p f)
	  o
	  (unshift_by n f))
  else
    ret false

(*
 * Bind the inductive hypotheses in an expanded constructor with parameters
 *
 * Assumes it's an expanded constructor, but doesn't check for structure
 * This also may fail if the IH is applied to something when we expand
 * So we should test for that case
 *)
let bind_ihs (c : proof_cat) =
  bind
    (context_at_index c 1)
    (fun context ->
      let env_with_p = context_env context in
      let (_, _, p) = CRD.to_tuple @@ lookup_rel 1 env_with_p in
      let env = pop_rel_context 1 env_with_p in
      apply_functor
	(fun o -> ret o)
	(branch_state
	   (map_dest (applies_ih env p c))
	   (map_ext_arrow (fun _ -> ret (fresh_ih ())))
	   ret)
	c)

(*
 * Expand an inductive constructor
 * That is, expand its conclusion fully if it is dependent
 * Then mark the edges that are inductive hypotheses
 *)
let expand_constr (c : proof_cat) =
  bind
    (expand_inductive_conclusions_fully c)
    (fun c ->
      bind
	(bind_ihs c)
	(fun c_exp ->
	  let ms = morphisms c_exp in
	  let assums = hypotheses ms in
	  let concls = conclusions ms in
	  bind
	    (all_objects_except_those_in assums concls)
	    (fun trs ->
	      let tr = List.hd trs in
	      bind
		(objects c_exp)
		(fun os -> make_category os ms (initial_opt c_exp) (Some tr)))))

