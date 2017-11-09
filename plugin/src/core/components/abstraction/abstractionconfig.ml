open Environ
open Term
open Abstracters
open Candidates
open Coqterms
open Debruijn
open Collections
open Searchopts
open Reducers
open Printing
open Proofdiff

(* --- Configuring Abstraction --- *)

(* Caller configuration for abstraction *)
(* TODO separate out configs for property and argument,
   instead of per strategy *)
(* Or just take base and goal applied *)
(* TODO hide from interface eventually, move configuring options here *)
type abstraction_config =
  {
    env : env;
    args_base : types list;
    args_goal : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : abstraction_strategy list;
  }

(* --- Common functionality --- *)

(*
 * Configure abstraction by a function given the environment,
 * the body of the goal, and the candidate
 *)
let rec configure_fun_goal_body strategies env goal c : abstraction_config =
  match kinds_of_terms (goal, c) with
  | (Prod (_, _, gb), Lambda (n, t, cb)) when isProd gb && isLambda cb ->
     configure_fun_goal_body strategies (push_rel (n, None, t) env) gb cb
  | (Prod (_, gt, gb), Lambda (_, _, _)) when isApp gt && isApp gb ->
     let (_, _, ctb) = destProd (infer_type env c) in
     if isApp ctb then
       let (f_base, _) = destApp (unshift ctb) in
       let f_goal = f_base in
       let args_base = Array.to_list (snd (destApp gt)) in
       let args_goal = List.map unshift (Array.to_list (snd (destApp gb))) in
       let cs = [c] in
       {env; args_base; args_goal; cs; f_base; f_goal; strategies}
     else
       failwith "Cannot infer function to abstract"
  | _ ->
     failwith "Goal is inconsistent with term to abstract" 

(* --- Defaults --- *)

(* Default strategies *)
let default_arg_strategies = reduce_strategies
let default_fun_strategies = reduce_strategies_prop

(*
 * Default configuration for abstracting arguments for a list of candidates,
 * given the difference in goals d_type in a common environment env
 *)
let configure_args env (d_type : types proof_diff) cs =
  let new_goal_type = new_proof d_type in
  let old_goal_type = old_proof d_type in
  let (f_base, args_n) = destApp new_goal_type in
  let (f_goal, _) = destApp old_goal_type in
  let args_base = Array.to_list args_n in
  let args_goal = args_base in
  let strategies = default_arg_strategies in
  {env; args_base; args_goal; cs; f_base; f_goal; strategies}

(*
 * Apply a dependent proposition at an index to the goal
 * This makes the call for fixpoint configuration consistent with the
 * top-level
 *)
let rec apply_prop pi goal =
  match kind_of_term goal with
  | Prod (n, t, b) when isProd b ->
     mkProd (n, t, apply_prop (shift_i pi) b)
  | Prod (n, t, b) ->
     let p = mkRel pi in
     let t_args = singleton_array t in
     let b_args = singleton_array b in
     mkProd (n, mkApp (p, t_args), mkApp (shift p, b_args))

(*
 * Get goals for abstraction by a function for a change in fixpoint cases
 * Take an environment, a list of differences between those cases,
 * and a list of candidates
 *)
let configure_fixpoint_cases env (diffs : types list) (cs : candidates) =
  let goals = List.map (apply_prop 1) diffs in
  flat_map
    (fun goal ->
      List.map (configure_fun_goal_body default_fun_strategies env goal) cs)
    goals

(* --- Cut Lemmas --- *)

(* Given some cut lemma application, configure arguments to abstract *)
let rec configure_args_cut_app env (app : types) cs : abstraction_config =
  match kind_of_term app with
  | Lambda (n, t, b) ->
     configure_args_cut_app (push_rel (n, None, t) env) b cs
  | App (f, args) ->
     let rec get_lemma_functions typ =
       match kind_of_term typ with
       | Prod (n, t, b) when isProd b ->
          let (f_base, f_goal) = get_lemma_functions b in
          (mkLambda (n, t, f_base), mkLambda (n, t, f_goal))
       | Prod (n, t, b) ->
          (t, unshift b)
       | _ ->
          failwith "Could not infer arguments to generalize"
     in
     let (f_base, f_goal) = get_lemma_functions (infer_type env f) in
     let args_base = Array.to_list args in
     let args_goal = args_base in
     let strategies = no_reduce_strategies in
     {env; args_base; args_goal; cs; f_base; f_goal; strategies}
  | _ ->
     failwith "Ill-formed cut lemma"

(* Configure abstraction over arguments when cutting by a cut lemma *)
let configure_cut_args env (cut : cut_lemma) (cs : candidates) =
  let cs = filter_consistent_cut env cut cs in
  if List.length cs > 0 then
    let (_, _, b) = destLambda (get_app cut) in
    let env_cut = push_rel (Anonymous, None, get_lemma cut) env in
    configure_args_cut_app env_cut b cs
  else
    failwith "No candidates are consistent with the cut lemma type"

(* --- Goals --- *)

(*
 * Configure abstracton by a function given the environment,
 * goal type, and the candidate
 *)
let configure_fun_from_goal env goal c : abstraction_config =
  let (_, _, goal_body) = destProd goal in
  configure_fun_goal_body default_fun_strategies env goal_body c
