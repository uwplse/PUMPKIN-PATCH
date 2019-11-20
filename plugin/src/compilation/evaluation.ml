(* --- Evaluation, which is lazy (takes one step) --- *)

open Constr
open Environ
open Evd
open Proofcat
open Proofcatterms
open Utilities
open Names
open Debruijn
open Declarations
open Indutils
open Contextutils
open Stateutils
open Inference
open Assumptions
open Envutils

(*
 * Note: Evar discipline is not good yet, but should wait until after
 * the major refactor, since this will change a lot.
 *)

(*
 * Evaluate typ one step in env
 * Then bind the single anonymous arrow to e
 *)
let eval_theorem_bind (e : extension) (env : env) (typ : types) =
  let t = Context (Term (typ, env), (fid ())) in
  bind
    (bind (bind initial_category (add_object t)) (set_terminal (Some t)))
    (fun c -> bind_cat c (initial_context, e, t))

(* Evaluate an anonymous proof of typ one step *)
let eval_theorem (env : env) (typ : types) =
  eval_theorem_bind AnonymousBinding env typ

(* Evaluate a proof trm one step *)
let eval_proof (env : env) (trm : types) sigma =
  let sigma, typ = infer_type env sigma trm in
  eval_theorem_bind (ext_of_term env trm) env typ sigma

(* Evaluate an arrow as a proof *)
let eval_proof_arrow (m : arrow) =
  let (_, e, dst) = m in
  eval_proof (context_env dst) (ext_term e)

(* --- Induction --- *)

(*
 * Get the induction principle tree divided by constructors
 *
 * When we test this, we should see if the unfolding limitation
 * we have right now always works, even when constructors have many internal
 * foralls.
 *)
let rec induction_constrs (nc : int) (env : env) ((n, t, b) : Name.t * types * types) =
  if nc = 0 then
    ret []
  else
    let e = LazyBinding (mkRel 1, push_rel CRD.(LocalAssum(n, t)) env) in
    bind 
      (eval_theorem_bind e env t)
      (fun c ->
	match kind b with
	| Prod (n', t', b') ->
	   let d = List.length (morphisms c) in
	   let prod' = (n', unshift_by d t', unshift_by d b') in
	   bind (induction_constrs (nc - 1) env prod') (fun cs -> ret (c :: cs))
	| _ ->
	   ret [c])

(*
 * Auxiliary function for eval_induction
 * Bind arguments in a list of constructors
 *)
let bind_constrs_to_args fc cs ncs elim =
  let constrs = Array.of_list elim.cs in
  let num_constrs = Array.length constrs in
  bind
    (map_state (substitute_terminal fc) cs)
    (fun ps ->
      let cs_params = Array.of_list ps in
      bind
	(bind_inductive_args constrs cs_params)
	(fun args ->
	  let cs_args = Array.to_list args in
	  let cs_no_args = List.map (Array.get cs_params) (range num_constrs (List.length cs)) in
	  ret (List.append cs_args cs_no_args)))

(*
 * Auxiliary function for eval_induction
 * Combine a list of constructors, defaulting to default
 * Assumes no terminal object
 *)
let combine_constrs (default : proof_cat) (cs : proof_cat list) =
  match cs with
  | h :: t -> 
     fold_left_state (combine (initial_opt h) None) h t
  | [] -> 
     ret default

(* --- TODO temp --- *)

(* Remove the initial object of c *)
let remove_initial (c : proof_cat) =
  let i = initial c in
  let ms = morphisms c in
  bind
    (bind (objects c) (all_objects_except i))
    (fun os' ->
      bind
        (partition_state (map_source (objects_not_equal i)) ms)
	(fun (ms', ims) ->
	  let (_, _, i') = List.hd ims in
	  make_category os' ms' (Some i') (terminal_opt c)))

(* Remove the first n contexts *)
let rec remove_first_n (n : int) (c : proof_cat) =
  if n = 0 then
    ret c
  else
    bind (remove_initial c) (remove_first_n (n - 1))

(*
 * Introduce n common elements of c1 and c2 if possible
 * Remove those elements from the premise of c1 and c2
 * Add them to assums
 *)
let intro_common_n n (c1, c2, assums) sigma =
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    sigma, None
  else
    let sigma, c1' = remove_first_n n c1 sigma in
    let sigma, c2' = remove_first_n n c2 sigma in
    sigma, Some (c1', c2', assume_local_n_equal n assums)

(*
 * Introduce a common element of c1 and c2 if possible
 * Remove that element from the premise of c1 and c2
 * Add it to assums
 *)
let intro_common = intro_common_n 1

(*
 * Introduce n elements of c1 and c2 if possible
 * Remove those elements from the premise of c1 and c2
 * Shift the assumptions
 *)
let intro_n n (c1, c2, assums) sigma =
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    sigma, None
  else
    let sigma, c1' = remove_first_n n c1 sigma in
    let sigma, c2' = remove_first_n n c2 sigma in
    sigma, Some (c1', c2', shift_assumptions_by n assums)

(*
 * Introduce an element of c1 and c2 if possible
 * Remove it from the premise of c1 and c2
 * Shift the assumptions
 *)
let intro = intro_n 1
         
(*
 * Introduce nparams parameters to an inductive diff d
  *
 * This assumes both proofs have the same number of parameters,
 * otherwise it will fail.
 *
 * TODO for now combining into one process; later consolidate by slowly
 * removing, until proof cats are gone
 *)
let intro_params nparams (o, n, assums) =
  bind
    (bind
       (params o nparams)
       (fun pms_o ->
	 bind
	   (params n nparams)
	   (fun pms_n ->
	     fold_right2_state
	       (fun (_, e1, _) (_, e2, _) d_opt ->
		 let d = Option.get d_opt in
		 branch_state
		   (fun (_, _, assums) -> extensions_equal_assums assums e1 e2)
		   intro_common
		   intro
		   d)
	       pms_o
	       pms_n
               (Some (o, n, assums)))))
    (fun o -> intro_common (Option.get o))

(* --- End TODO --- *)

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
    
(*
 * Expand a term exactly once
 * Default to using f when it cannot be expanded further
 * Error if the type context doesn't hold any terms
 * TODO temporary
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
    
(*
 * Expand the terminal object of c exactly once
 * Return c if it cannot be expanded
 * TODO temporary
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

(* For an inductive proof, expand n inductive parameters and the principle P
  TODO temporary *)
let expand_inductive_params (n : int) (c : proof_cat) =
  let rec expand n' c' =
    if n' < 0 || (not (context_is_product (terminal c'))) then
      ret c'
    else
      bind (expand_terminal c') (expand (n' - 1))
  in expand n c

(*
 * Evaluate an inductive proof
 * Bind the arguments to the application of the induction principle
 * Return any leftover arguments after induction
 *)
let eval_induction (mutind_body_o, mutind_body_n) assums (fc_o, fc_n) elims =
  let npms = mutind_body_o.mind_nparams in
  let eval_induction_1 mutind_body assums fc elim =
    let t = terminal fc in
    if context_is_product t then
      let ncs = num_constrs mutind_body in
      let motive = elim.p in
      let params = elim.pms in
      bind
        (induction_constrs ncs (context_env t) (context_as_product t))
        (fun cs ->
	  bind
	    (bind 
	       (bind_constrs_to_args fc cs ncs elim)
	       (combine_constrs fc))
	    (bind_property_and_params (Some motive) params npms))
    else
      ret fc
  in
  bind
    (eval_induction_1 mutind_body_o assums fc_o (fst elims))
    (fun c_o ->
      bind
        (eval_induction_1 mutind_body_n assums fc_n (snd elims))
        (fun c_n ->
          bind
            (intro_params npms (c_o, c_n, assums))
            (fun o -> ret (Option.get o))))
            
(*
 * TODO temporary; probably the last to go since it is the most complicated
 * compiles inductive proofs into trees
 *)
let eval_induction_cat assums envs elims =
  let f_o, f_n = (map_tuple (fun e -> e.elim) elims) in
  try
    let (c_o, u_o), (c_n, u_n) = map_tuple destConst (f_o, f_n) in
    let mutind_o = Option.get (inductive_of_elim (fst envs) (c_o, u_o)) in
    let mutind_n = Option.get (inductive_of_elim (snd envs) (c_n, u_n)) in
    let mutind_body_o = lookup_mind mutind_o (fst envs) in
    let mutind_body_n = lookup_mind mutind_n (snd envs) in
     bind
       (bind
	  (eval_proof (fst envs) f_o)
	  (fun c_o ->
            bind
              (eval_proof (snd envs) f_n)
              (fun c_n sigma ->
                let sigma, f_exp_o = expand_inductive_params mutind_body_o.mind_nparams c_o sigma in
                let sigma, f_exp_n = expand_inductive_params mutind_body_n.mind_nparams c_n sigma in
                sigma, (f_exp_o, f_exp_n))))
       (fun (f_exp_o, f_exp_n) ->
	 eval_induction (mutind_body_o, mutind_body_n) assums (f_exp_o, f_exp_n) elims)
  with _ ->
    failwith "Not an inductive proof"
