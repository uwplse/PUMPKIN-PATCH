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
 * A partitition of arguments to an inductive proof into four parts:
 * 1. A list of inductive parameters
 * 2. An optional inductive property
 * 3. A list of non-parameter arguments to the induction principle
 * 4. A list of arguments that follow the entire application of the principle
 *
 * Because of partial application, any of these may be empty/None.
 *)
type 'a argument_partition =
  {
    params : 'a list;
    property : 'a option;
    non_params : 'a list;
    final_args : 'a list;
  }

(*
 * Partition arguments to an inductive proof into parts.
 * nparams is the number of parameters in the inductive type.
 * nconstrs is the number of constructors in the inductive type.
 * args is the list of arguments before partition.
 *)
let partition_args (nparams : int) (nconstrs : int) (args : 'a list) : 'a argument_partition =
  let (params, rest) = split_at nparams args in
  match rest with
  | h :: t ->
     let property = Some h in
     let (non_params, final_args) = split_at nconstrs t in
     {params; property; non_params; final_args}
  | [] ->
     let property = None in
     let (non_params, final_args) = ([], []) in
     {params; property; non_params; final_args}

(*
 * Auxiliary function for eval_induction
 * Bind arguments in a list of constructors
 *)
let bind_constrs_to_args fc cs ncs arg_partition =
  let non_params = Array.of_list arg_partition.non_params in
  let num_non_params = Array.length non_params in
  bind
    (map_state (substitute_terminal fc) cs)
    (fun ps ->
      let cs_params = Array.of_list ps in
      bind
	(bind_inductive_args non_params cs_params)
	(fun args ->
	  let cs_args = Array.to_list args in
	  let cs_no_args = List.map (Array.get cs_params) (range num_non_params (List.length cs)) in
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
         
(*
 * Evaluate an inductive proof
 * Bind the arguments to the application of the induction principle
 * Return any leftover arguments after induction
 *)
let eval_induction (mutind_body_o, mutind_body_n) assums (fc_o, fc_n) (args_o, args_n) =
  let npms = mutind_body_o.mind_nparams in
  let eval_induction_1 mutind_body assums fc args =
    let t = terminal fc in
    if context_is_product t then
      let ncs = num_constrs mutind_body in
      let arg_partition = partition_args npms ncs (Array.to_list args) in
      let property = arg_partition.property in
      let params = arg_partition.params in
      bind
        (induction_constrs ncs (context_env t) (context_as_product t))
        (fun cs ->
	  bind
	    (bind 
	       (bind_constrs_to_args fc cs ncs arg_partition)
	       (combine_constrs fc))
	    (bind_property_and_params property params npms))
    else
      ret fc
  in
  bind
    (eval_induction_1 mutind_body_o assums fc_o args_o)
    (fun c_o ->
      bind
        (eval_induction_1 mutind_body_n assums fc_n args_n)
        (fun c_n ->
          bind
            (intro_params npms (c_o, c_n, assums))
            (fun o -> ret (Option.get o))))
