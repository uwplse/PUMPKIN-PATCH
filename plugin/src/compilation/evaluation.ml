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
open Checking

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
let expand_term (default : env -> types -> evar_map -> proof_cat state) env trm =
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
	   (expand_term (eval_theorem_bind binding) env trm) 
	   (substitute_terminal c))
  | _ ->
     ret c

(* For an inductive proof, expand n inductive parameters and the principle P
  TODO temporary *)
let eval_inductive_params (n : int) env f =
  let rec expand n c =
    if n < 0 then
      ret c
    else
      bind (expand_terminal c) (expand (n - 1))
  in bind (eval_proof env f) (expand n)

(*
 * TODO
 *)
let bind_apply_function (e : extension) (n : int) ms =
  let args = List.rev (List.map (fun i -> Index i) (from_one_to n)) in
  let binding = List.fold_left (fun b r -> AppBinding (b, r)) e args in
  let (_, _, t) = last ms in
  map_state
    (branch_state
       (maps_to t)
       (fun (src, _, dst) -> ret (src, binding, dst))
       ret)
    ms
          
(*
 * Utility function for expanding inductive proofs
 * Expand conclusions of different cases of an inductive proof that are dependent
 *)
let expand_inductive_conclusions (ms : arrow list) sigma =
  flat_map_state
    (fun (s, e, d) ->
      bind
	(expand_product_fully d)
	(fun dc ->
          let ms = morphisms dc in
          let (_, _, t) = last ms in
          let i = initial dc in
	  let map_i_to_src = 
	    branch_state (objects_equal i) (fun _ -> ret s) ret
	  in
	  let arity = List.length ms - 1 in
	  let env = substitute_ext_env (context_env t) e in
          bind
	    (map_state (map_source_arrow map_i_to_src) ms)
	    (bind_apply_function (shift_ext_by arity env) arity)))
    ms
    sigma

(*
 * TODO move to lib if we still need this after refactor to remove cats
 * TODO temp
 *)
let find_off (a : 'a list) (p : 'a -> evar_map -> bool state) sigma : int state =
  let rec find_rec a p n =
    match a with
    | [] -> failwith "not found"
    | h :: tl ->
       branch_state
         p
         (fun _ -> ret n)
         (fun _ -> find_rec tl p (n + 1))
         h
  in find_rec a p 0 sigma

(*
 * TODO temp
 *)
let arrows_with_source env src ms =
  List.filter (fun ((src', env'), _, _) -> equal src src' && nb_rel env = nb_rel env') ms
              
(*
 * Find ordered paths from src to dst in c via explicit arrows
 * TODO temp
 *)
let rec path_length_between ms env src dst =
  if equal src dst then
    0
  else
    let ms_from_s = arrows_with_source env src ms in
    if List.length ms_from_s = 0 then
      0
    else
      let (_, _, (src, env)) = List.hd ms_from_s in
      let path_length = path_length_between ms env src dst in
      1 + path_length

(* Check if an o is the type of an applied inductive hypothesis in c *)
let applies_ih (env : env) (p : types) ms i t =
  if isApp t then
    let (f, _) = destApp t in
    let n = path_length_between ms env i t in
    let hs = List.map (fun ((src, _), _, _) -> src) ms in
    and_state 
      (fun t -> exists_state (fun h -> ret (equal h t)) hs)
      (fun f sigma -> has_type env sigma p f)
      t
      (unshift_by n f)
  else
    ret false
          
(*
 * Expand an inductive constructor
 * That is, expand its conclusion fully if it is dependent
 * Then mark the edges that are inductive hypotheses
 *)
let expand_constr ms sigma =
  let (src, _, dst) = List.hd ms in
  let sigma, (ms_to_expand, old_ms) =
    partition_state
      (map_dest 
         (fun o ->
	   and_state
	     (fun o -> ret (context_is_product o)) 
	     (not_state (fun o -> contains_object o (hypotheses ms)))
	     o
	     o))
      ms
      sigma
  in
  let sigma, new_ms = expand_inductive_conclusions ms_to_expand sigma in
  let ms = List.map (fun (src, e, dst) -> dest_context_term src, ext_term e, dest_context_term dst) (List.append old_ms new_ms) in
  let sigma, (ms_ihs, ms_filtered) =
    let env_with_p = context_env dst in
    let (_, _, p) = CRD.to_tuple @@ lookup_rel 1 env_with_p in
    let env = pop_rel_context 1 env_with_p in
    partition_state
      (fun (_, _, dst) -> applies_ih env p ms (context_term src) (fst dst))
      ms
      sigma
  in
  let (_, _, (goal, env)) = last ms in
  let c_dsts = List.map (fun (_, _, dst) -> dst) (all_but_last ms_filtered) in
  let c_envs = List.map snd c_dsts in
  let c_goals = List.map fst c_dsts in
  let c_terms = List.map (fun (_, e, _) -> e) ms_filtered in
  let num_ihs = List.length ms_ihs in
  sigma, (env, goal, c_envs, c_terms, c_goals, num_ihs)

(*
 * Evaluate an inductive proof
 * Bind the arguments to the application of the induction principle
 * Return any leftover arguments after induction
 * 
 * TODO hodgepodge of all of the old proofcat stuff left, so that we can
 * delete it at some point once we figure out what it is doing in terms of
 * environments and terms
 *)
let eval_induction_data assums envs elims sigma =
  let f_o, f_n = (map_tuple (fun e -> e.elim) elims) in
  let env_o, env_n = envs in
  try
    let npms = List.length ((fst elims).pms) in
    let eval_induction_1 assums env f elim sigma =
      let sigma, fc = eval_inductive_params npms env f sigma in
      let t = terminal fc in
      let sigma, c =
        if context_is_product t then
          let ncs = List.length (elim.cs) in
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
            sigma
        else
          ret fc sigma
      in
      let sigma, c = remove_first_n (npms + 1) c sigma in
      bind (split c) (map_state (fun c -> expand_constr (morphisms c))) sigma
    in
    let assums = assume_local_n_equal (npms + 1) assums in
    let sigma, os = eval_induction_1 assums env_o f_o (fst elims) sigma in
    let sigma, ns = eval_induction_1 assums env_n f_n (snd elims) sigma in
    let cases_data =
      List.map2
        (fun o n ->
          let (env_o, goal_o, c_envs_o, c_terms_o, c_goals_o, num_ihs) = o in
          let (env_n, goal_n, c_envs_n, c_terms_n, c_goals_n, _) = n in
          let envs = env_o, env_n in
          let goals = goal_o, goal_n in
          let c_envs = c_envs_o, c_envs_n in
          let c_terms = c_terms_o, c_terms_n in
          let c_goals = c_goals_o, c_goals_n in
          (envs, goals, c_envs, c_terms, c_goals, num_ihs))
        os
        ns
    in sigma, (assums, cases_data)
  with _ ->
    failwith "Not an inductive proof"
