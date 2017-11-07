(* --- Abstraction Component --- *)

(* TODO there is still code in here to check and clean up *)

open Abstracters
open Environ
open Term
open Debruijn
open Coqterms
open Printing
open Collections
open Reducers
open Specialization
open Coqenvs
open Utilities
open Candidates

(* Caller configuration for abstraction *)
type abstraction_config =
  {
    is_concrete : bool; (* TODO hack *)
    env : env;
    args : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : abstraction_strategy list;
  }

(* Internal options for abstraction *)
type abstraction_options =
  {
    concrete : closure;
    abstract : closure;
    goal_type : types;
    num_to_abstract : int;
  }

(* --- Functionality for abstraction --- *)

(*
 * Wrap each candidate in a lambda from anonymous terms with the types of args
 * Assumes all arguments are bound in env
 *)
let generalize (env : env) (num_to_abstract : int) (cs : candidates) : candidates =
  snd
    (List.fold_right
       (fun _ (en, l) ->
         let typ = unshift (infer_type en (mkRel 1)) in
         let env_pop = Environ.pop_rel_context 1 en in
         (env_pop, List.map (fun b -> mkLambda (Anonymous, typ, b)) l))
       (range 1 (num_to_abstract + 1))
       (env, cs))

(*
 * From a common environment, source type, destination type,
 * and number of arguments, get the goal type for abstraction
 * that takes you from destination back to source,
 * abstracting over the arguments
 *
 * TODO does this expect a certain form? Like reduced? If so, document
 * Also, right now, abstraction fails if t_b t_g aren't convertible,
 * should document somewhere too, but not checking for efficiency and
 * simplicity
 *)
let get_arg_abstract_goal_type (config : abstraction_config) (num_args : int) : types =
  let rec infer_goal (b : types) (g : types) : types =
    match (kind_of_term b, kind_of_term g) with
    | (Lambda (n_b, t_b, b_b), Lambda (_, t_g, b_g)) ->
       mkProd (n_b, t_b, infer_goal b_b b_g)
    | (Prod (n_b, t_b, b_b), Prod (_, t_g, b_g)) ->
       mkProd (n_b, t_b, infer_goal b_b b_g)
    | _ ->
       mkProd (Anonymous, b, shift g)
  in infer_goal config.f_base config.f_goal

(*
 * When abstracting over a property, add the property itself to the arguments
 * to abstract over
 *)
let get_concrete_prop (config : abstraction_config) (concrete : closure) : closure =
  let (env, args) = concrete in
  let p = config.f_base in
  let p_typ = infer_type env p in
  let num_args = nb_rel env in
  let env_p =
    List.fold_left
      (fun env (n, b, t) ->
        push_rel (n, b, t) env)
      (push_rel (Anonymous, None, p_typ) (pop_rel_context num_args env))
      (lookup_rels (List.rev (from_one_to num_args)) env)
  in (env_p, p :: (List.tl args))

(* Get the concrete environment and arguments to abstract *)
let get_concrete config strategy : closure =
  let env = config.env in
  let args = config.args in
  let s = reducer_to_specializer reduce_term in
  let base = specialize_using s env config.f_base (Array.of_list args) in
  let concrete = (env, List.append args [base]) in
  match kind_of_abstraction strategy with
  | Arguments ->
     concrete
  | Property _ ->
     get_concrete_prop config concrete

(* Get abstract arguments for a function *)
let get_abstraction_args config : closure =
  let rec infer_args (i : int) (en : env) (g : types) : closure =
    if i = 0 then
      (en, [])
    else
      match kind_of_term g with
      | Lambda (n, t, b) ->
	 let en' = push_rel (n, None, t) en in
	 let (en'', b') = infer_args (i - 1) en' b in
	 (en'', (mkRel i) :: b')
      | _ ->
	 (en, [])
  in infer_args (List.length config.args) config.env config.f_goal

(* Get the abstract arguments that map to concrete arguments
   for a particular strategy, function, and arguments *)
let get_abstract config concrete strategy : closure =
  let s = reducer_to_specializer reduce_term in
  match kind_of_abstraction strategy with
  | Arguments ->
     let (env_abs, args_abs) = get_abstraction_args config in
     let p = shift_by (List.length args_abs) config.f_base in
     let base_abs = specialize_using s env_abs p (Array.of_list args_abs) in
     (env_abs, List.append args_abs [base_abs])
  | Property _ ->
     let args_abs = config.args in
     let (env_p, args_p) = concrete in
     let p = mkRel (List.length args_p) in
     let base_abs = specialize_using s env_p p (Array.of_list args_abs) in
     (env_p, List.append (p :: List.tl args_abs) [base_abs])

(* Given a abstraction strategy, get the abstraction options for the
   particular function and arguments *)
let get_abstraction_opts config strategy : abstraction_options =
  let concrete = get_concrete config strategy in
  let abstract = get_abstract config concrete strategy in
  match kind_of_abstraction strategy with
  | Arguments ->
     let num_to_abstract = List.length config.args in
     let goal_type = get_arg_abstract_goal_type config num_to_abstract in
     { concrete; abstract; goal_type; num_to_abstract }
  | Property goal_type ->
     let (_, args_p) = concrete in
     let num_to_abstract = List.length args_p in
     { concrete; abstract; goal_type; num_to_abstract }

(*
 * Given a strategy, return a function that optionally shifts concrete terms
 *
 * This is probably temporary since property abstraction is only called outside
 * of an algorithm right now in a tactic, and so the concrete and abstract
 * are not offset from each other, unlike in the argument case
 *)
let shift_terms is_concrete strategy opts : types list -> types list =
  match kind_of_abstraction strategy with
  | Arguments ->
     if is_concrete then
       List.map (shift_by opts.num_to_abstract)
     else
       List.map id
  | Property _ ->
     List.map id

(* Abstract candidates with a provided abstraction strategy *)
let abstract_with_strategy (config : abstraction_config) strategy : candidates =
  let opts = get_abstraction_opts config strategy in
  let (env, args) = opts.concrete in
  let (env_abs, args_abs) = opts.abstract in
  let reduced_cs = reduce_all_using strategy env config.cs in
  let shift_concrete = shift_terms config.is_concrete strategy opts in
  let args_adj = shift_concrete args in
  let cs_adj = shift_concrete reduced_cs in
  let bs = substitute_using strategy env_abs args_adj args_abs cs_adj in
  let lambdas = generalize env_abs opts.num_to_abstract bs in
  Printf.printf "%d abstracted candidates\n" (List.length lambdas);
  filter_using strategy env opts.goal_type lambdas

(*
 * Try to abstract candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *
 * TODO clean types after generalizing w args
 *)
let abstract_with_strategies (config : abstraction_config) : candidates =
  let abstract_using = abstract_with_strategy config in
  let rec try_abstract_using strategies =
    match strategies with
    | h :: t ->
       let abstracted = abstract_using h in
       if (List.length abstracted) > 0 then
         abstracted
       else
         try_abstract_using t
    | _ ->
       []
  in try_abstract_using config.strategies
