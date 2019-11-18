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

(* --- Type definitions --- *)

type 'a expansion_strategy = 'a -> evar_map -> 'a state

(* --- Terms and types --- *)

(* Expand a product type exactly once *)
let expand_product (env : env) ((n, t, b) : Name.t * types * types) =
  bind
    (eval_theorem env t)
    (fun t' ->
      let env' = push_local (n, t) env in
      bind
	(bind (eval_theorem env' b) (substitute_categories t'))
	(fun c ->
	  bind_cat c (initial c, LazyBinding (mkRel 1, env'), terminal t')))

(* Expand a lambda term exactly once *)
let expand_lambda (env : env) ((n, t, b) : Name.t * types * types) =
  expand_product env (n, t, b)

(*
 * Expand an inductive type
 * This is unfinished, and currently unused for any benchmarks
*)
let expand_inductive (env : env) (((i, ii), u) : pinductive) =
  let mbody = lookup_mind i env in
  check_inductive_supported mbody;
  let bodies = mbody.mind_packets in
  let env_ind = push_rel_context (bindings_for_inductive env mbody bodies) env in
  let body = bodies.(ii) in
  let constrs =
    List.map
      (fun ci -> mkConstructU (((i, ii), ci), u))
      (from_one_to (Array.length body.mind_consnames))
  in
  bind
    (map_state (eval_proof env_ind) constrs)
    (fun cs ->
      fold_left_state
	(fun cind c ->
	  let ms = List.append (morphisms c) (morphisms cind) in
	  bind 
	    (bind (objects cind) (fun tl -> ret (terminal c :: tl)))
	    (fun os -> make_category os ms (initial_opt cind) None))
	(List.hd cs)
	(List.tl cs))

(*
 * Expand application exactly once
 * Assumes there is at least one argument
 *)
let expand_app (env : env) ((f, args) : types * types array) =
  assert (Array.length args > 0);
  let arg = args.(0) in
  bind
    (eval_proof env (mkApp (f, Array.make 1 arg)))
    (fun f' ->
      bind
	(bind (eval_proof env arg) (fun c -> substitute_categories c f'))
	(bind_apply_function (LazyBinding (f, env)) 1))

(* --- Contexts --- *)

(*
 * Expand a term exactly once
 * Default to using f when it cannot be expanded further
 * Error if the type context doesn't hold any terms
 *)
let expand_term (default : env -> types -> evar_map -> proof_cat state) (o : context_object) =
  let (trm, env) = dest_context_term o in
  match kind trm with
  | Prod (n, t, b) ->
     expand_product env (n, t, b)
  | Lambda (n, t, b) ->
     expand_lambda env (n, t, b)
  | Ind ((i, ii), u) ->
     expand_inductive env ((i, ii), u)
  | App (f, args) ->
     (match kind f with
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
let expand_product_fully (o : context_object) =
  let rec expand_fully env (n, t, b) =
    match kind b with
    | Prod (n', t', b') ->
       bind
	 (eval_theorem env t)
	 (fun t'' ->
	   let env' = push_local (n, t) env in
	   bind
	     (bind (expand_fully env' (n', t', b')) (substitute_categories t''))
	     (fun c ->
	       let init_o = initial c in
	       let term_o = terminal t'' in
	       bind_cat c (init_o, LazyBinding (mkRel 1, env'), term_o)))
    | _ ->
       expand_product env (n, t, b)
  in expand_fully (context_env o) (destProd (fst (dest_context_term o)))

(* --- Categories --- *)

(*
 * Expand the terminal object of c exactly once
 * Return c if it cannot be expanded
 *)
let expand_terminal (c : proof_cat) =
  let t = terminal c in
  match t with
  | Context (Term (trm, env), i) ->
     let ms = morphisms c in
     bind
       (arrows_with_dest t ms)
       (fun concls ->
	 let binding =
	   if non_empty concls then
             let (_, ext, _) = List.hd concls in (* arbitrary for now *)
             ext
	   else
             AnonymousBinding
	 in
	 bind 
	   (expand_term (eval_theorem_bind binding) t) 
	   (substitute_terminal c))
  | _ ->
     ret c

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


(* For an inductive proof, expand n inductive parameters and the principle P *)
let expand_inductive_params (n : int) (c : proof_cat) =
  let rec expand n' c' =
    if n' < 0 || (not (context_is_product (terminal c'))) then
      ret c'
    else
      bind (expand_terminal c') (expand (n' - 1))
  in expand n c

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
       
(*
 * TODO temporary; probably the last to go since it is the most complicated
 * compiles inductive proofs into trees
 *)
let eval_induction_cat env trm =
  let (f, args) = destApp trm in
  try
    let (c, u) = destConst f in
    let mutind = Option.get (inductive_of_elim env (c, u)) in
    let mutind_body = lookup_mind mutind env in
     bind
       (bind
	  (eval_proof env f)
	  (expand_inductive_params mutind_body.mind_nparams))
       (fun f_exp ->
	 eval_induction mutind_body f_exp args)
  with _ ->
    failwith "Not an inductive proof"
