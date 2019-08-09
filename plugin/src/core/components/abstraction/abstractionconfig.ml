open Environ
open Evd
open Constr
open Abstracters
open Candidates
open Debruijn
open Utilities
open Proofdiff
open Cutlemma
open Contextutils
open Envutils
open Inference

(* --- Configuring Abstraction --- *)

(* Caller configuration for abstraction *)
(* TODO separate out configs for property and argument,
   instead of per strategy *)
(* Or just take base and goal applied *)
(* TODO hide from interface eventually, move configuring options here *)
type abstraction_config =
  {
    env : env;
    evd : evar_map;
    args_base : types list;
    args_goal : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : abstraction_strategy list;
  }

(* --- Common functionality --- *)

(* Default strategies *)
let default_arg_strategies = reduce_strategies
let default_fun_strategies = reduce_strategies_prop

(*
 * Configure abstraction by a function or arguments given the environment,
 * the body of the goal, and the candidate
 *
 * TODO clean and document arg case
 *)
let rec configure_goal_body env evd goal c : abstraction_config =
  match map_tuple kind (goal, c) with
  | (Prod (_, _, gb), Lambda (n, t, cb)) when isProd gb && isLambda cb ->
     configure_goal_body (push_rel CRD.(LocalAssum(n, t)) env) evd gb cb
  | (Prod (_, gt, gb), Lambda (_, _, _)) when isApp gt && isApp gb ->
     let evd, c_typ = infer_type env evd c in
     let (_, ctt, ctb) = destProd c_typ in
     if isApp ctb then
       let cs = [c] in
       let args_base = Array.to_list (snd (destApp gt)) in
       let open Printing in
       debug_terms (push_local (Anonymous, ctt) env) (Array.to_list (snd (destApp gb))) "args_goal";
       debug_terms env (List.map unshift (Array.to_list (snd (destApp gb)))) "args_goal unshifted";
       let args_goal = List.map unshift (Array.to_list (snd (destApp gb))) in
       if List.for_all2 equal args_base args_goal then (* argument *)
	 if isApp ctt then
	   let f_goal = unshift (unwrap_definition env (fst (destApp gb))) in
	   let f_base = unwrap_definition env (fst (destApp gt)) in
	   let (_, args_base) = destApp ctt in
	   let args_base = Array.to_list args_base in
	   let args_goal = args_base in
	   let f_goal = unwrap_definition env f_goal in
	   let strategies = default_arg_strategies in
	   {env; evd; args_base; args_goal; cs; f_base; f_goal; strategies}
	 else
	   failwith "Cannot infer argument to abstract"
       else (* function *)
	 let f_base = unwrap_definition env (fst (destApp (unshift ctb))) in
	 let f_goal = f_base in
	 let strategies = default_fun_strategies in
	 {env; evd; args_base; args_goal; cs; f_base; f_goal; strategies}
     else
       failwith "Cannot infer function or argument to abstract"
  | _ ->
     failwith "Goal is inconsistent with term to abstract" 

(* --- Defaults --- *)

(*
 * Default configuration for abstracting arguments for a list of candidates,
 * given the difference in goals d_type in a common environment env
 *)
let configure_args env evd (d_type : types proof_diff) cs =
  let new_goal_type = new_proof d_type in
  let old_goal_type = old_proof d_type in
  let (f_base, args_n) = destApp new_goal_type in
  let (f_goal, _) = destApp old_goal_type in
  let args_base = Array.to_list args_n in
  let args_goal = args_base in
  let strategies = default_arg_strategies in
  {env; evd; args_base; args_goal; cs; f_base; f_goal; strategies}

(*
 * Apply a dependent proposition at an index to the goal
 * This makes the call for fixpoint configuration consistent with the
 * top-level
 *)
let rec apply_prop pi goal =
  match kind goal with
  | Prod (n, t, b) when isProd b ->
     mkProd (n, t, apply_prop (shift_i pi) b)
  | Prod (n, t, b) ->
     let p = mkRel pi in
     let t_args = Array.make 1 t in
     let b_args = Array.make 1 b in
     mkProd (n, mkApp (p, t_args), mkApp (shift p, b_args))
  | _ ->
     failwith "called apply_prop on a non-product"

(*
 * Push the function to abstract into the environment
 *
 * We should check this is actually well-typed
 *)
let rec push_prop env evd typ : env =
  match kind typ with
  | Prod (n, t, b) ->
     push_prop (push_rel CRD.(LocalAssum(n, t)) env) evd b
  | App (f, _) ->
     let evd, f_typ = infer_type env evd f in
     push_rel
       CRD.(LocalAssum(Names.Name.Anonymous, f_typ))
       (pop_rel_context (nb_rel env) env)
  | _ ->
     failwith "Could not find function to abstract"

(*
 * Get goals for abstraction by a function for a change in fixpoint cases
 * Take an environment, a list of differences between those cases,
 * and a list of candidates
 *)
let configure_fixpoint_cases env evd (diffs : types list) (cs : candidates) =
  let goals = List.map (apply_prop 1) diffs in
  flat_map
    (fun goal ->
      List.map
	(fun c ->
          let evd, prop = infer_type env evd c in
          let env_prop = push_prop env evd prop in
	  configure_goal_body env_prop evd goal c)
	cs)
    goals

(* --- Cut Lemmas --- *)

(* Given some cut lemma application, configure arguments to abstract *)
let rec configure_args_cut_app env evd (app : types) cs : abstraction_config =
  match kind app with
  | Lambda (n, t, b) ->
     configure_args_cut_app (push_rel CRD.(LocalAssum(n, t)) env) evd b cs
  | App (f, args) ->
     let rec get_lemma_functions typ =
       match kind typ with
       | Prod (n, t, b) when isProd b ->
          let (f_base, f_goal) = get_lemma_functions b in
          (mkLambda (n, t, f_base), mkLambda (n, t, f_goal))
       | Prod (n, t, b) ->
          (t, unshift b)
       | _ ->
          failwith "Could not infer arguments to generalize"
     in
     let evd, f_typ = infer_type env evd f in
     let (f_base, f_goal) = get_lemma_functions f_typ in
     let args_base = Array.to_list args in
     let args_goal = args_base in
     let strategies = no_reduce_strategies in
     {env; evd; args_base; args_goal; cs; f_base; f_goal; strategies}
  | _ ->
     failwith "Ill-formed cut lemma"

(* Configure abstraction over arguments when cutting by a cut lemma *)
let configure_cut_args env evd (cut : cut_lemma) (cs : candidates) =
  let cs = filter_consistent_cut env cut cs in
  if List.length cs > 0 then
    let (_, _, b) = destLambda (get_app cut) in
    let env_cut = push_rel CRD.(LocalAssum(Names.Name.Anonymous, get_lemma cut)) env in
    configure_args_cut_app env_cut evd b cs
  else
    failwith "No candidates are consistent with the cut lemma type"

(* --- Goals --- *)

(*
 * Configure abstracton by a function or arguments given the environment,
 * goal type, and the candidate
 *
 * Eventually, we would like to handle multiple cs without
 * one configuration for each c. Same for the fixpoint case.
 *)
let configure_from_goal env evd goal c : abstraction_config =
  let (n, t, goal_body) = destProd goal in
  configure_goal_body (push_rel CRD.(LocalAssum(n, t)) env) evd goal_body c

