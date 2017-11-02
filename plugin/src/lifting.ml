(* Lifting strategies *)

(* TODO there is still code in here to check and clean up *)

open Abstraction
open Environ
open Term
open Debruijn
open Filters
open Coqterms
open Printing
open Collections
open Specialization
open Coqenvs
open Utilities

type candidates = types list
type arg_subst = closure * closure

type lift_dimension = Arguments | Property of types

type lifting_strategy =
  {
    reducer : reducer;
    abstracter : abstraction_strategy;
    filter : types filter_strategy;
    to_lift : lift_dimension;
  }

(* User configuration for lifting *)
type lift_config =
  {
    is_concrete : bool; (* TODO hack *)
    env : env;
    args : types list;
    cs : candidates;
    f_base : types;
    f_goal : types;
    strategies : lifting_strategy list;
  }

(* Internal options for lifting *)
type lifting_options =
  {
    concrete : closure;
    abstract : closure;
    goal_type : types;
    num_to_abstract : int;
  }

(* --- Strategies for lifting arguments --- *)

(*
 * Reduce first
 * Replace all convertible terms at the highest level with abstracted terms
 *)
let syntactic_full_reduce : lifting_strategy =
  {
    reducer = reduce_term;
    abstracter = syntactic_full_strategy;
    filter = filter_by_type;
    to_lift = Arguments;
  }

(*
 * Don't reduce
 * Replace all convertible terms at the highest level with abstracted terms
 *)
let syntactic_full_no_reduce : lifting_strategy =
  {syntactic_full_reduce with reducer = remove_identities; }

(*
 * Reduce first
 * Replace all terms with convertible types at the highest level
 * with abstracted terms
 *)
let types_full_reduce : lifting_strategy =
  {
    reducer = reduce_term;
    abstracter = types_full_strategy;
    filter = filter_by_type;
    to_lift = Arguments;
  }

(*
 * Don't reduce
 * Replace all convertible terms at the highest level with abstracted terms
 *)
let types_full_no_reduce : lifting_strategy =
  { types_full_reduce with reducer = remove_identities; }

(*
 * Reduce first
 * Replace all terms matching a pattern (f, args) with abstracted terms
 * Fall back to syntactic_full when the concrete argument is not a pattern
 *)
let pattern_full_reduce : lifting_strategy =
  {
    reducer = reduce_term;
    abstracter = pattern_full_strategy;
    filter = filter_by_type;
    to_lift = Arguments;
  }

(*
 * Don't reduce
 * Replace all terms matching a pattern (f, args) with abstracted terms
 * Fall back to syntactic_full when the concrete argument is not a pattern
 *)
let pattern_no_reduce : lifting_strategy =
  { pattern_full_reduce with reducer = remove_identities; }

(*
 * Reduce first
 * Replace all combinations of convertible subterms with abstracted terms
 *)
let syntactic_all_reduce : lifting_strategy =
  {
    reducer = reduce_term;
    abstracter = syntactic_all_strategy;
    filter = filter_by_type;
    to_lift = Arguments;
  }

(*
 * Don't reduce
 * Replace all combinations of convertible subterms with abstracted terms
 *)
let syntactic_all_no_reduce : lifting_strategy =
  { syntactic_all_reduce with reducer = remove_identities; }

(*
 * All strategies that reduce first
 *)
let reduce_strategies : lifting_strategy list =
  [syntactic_full_reduce; syntactic_all_reduce; pattern_full_reduce]

(*
 * All strategies that don't reduce first
 *)
let no_reduce_strategies : lifting_strategy list =
  [syntactic_full_no_reduce; syntactic_all_no_reduce; pattern_no_reduce]

(*
 * List of default strategies
 *)
let default_strategies : lifting_strategy list =
  [syntactic_full_no_reduce; syntactic_full_reduce; pattern_full_reduce;
   syntactic_all_no_reduce; syntactic_all_reduce; pattern_no_reduce]

(*
 * List of the simplest strategies
 *)
let simple_strategies : lifting_strategy list =
  [syntactic_full_reduce; syntactic_full_no_reduce]

(* --- Strategies for lifting properties --- *)

let types_full_reduce_prop (goal : types) : lifting_strategy =
  { types_full_reduce with to_lift = Property goal; }

let types_full_no_reduce_prop (goal : types) : lifting_strategy =
  { types_full_no_reduce with to_lift = Property goal; }

let reduce_strategies_prop (goal : types) : lifting_strategy list =
  [types_full_reduce_prop goal]

let no_reduce_strategies_prop (goal : types) : lifting_strategy list =
  [types_full_no_reduce_prop goal]

let default_strategies_prop (goal : types) : lifting_strategy list =
  List.append
    (reduce_strategies_prop goal)
    (no_reduce_strategies_prop goal)

(* --- Functionality for lifting --- *)

(*
 * From the abstract environment, abstract args,
 * concrete environment, and concrete args,
 * return an argument substitution for lifting
 *)
let make_arg_subst (abstract : closure) (concrete : closure) =
  (abstract, concrete)

(*
 * Wrap each candidate in a lambda from anonymous terms with the types of args
 * Assumes all arguments are bound in env
 *)
let wrap_candidates_in_lambdas (env : env) (num_to_abstract : int) (cs : candidates) : candidates =
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
 * and number of arguments, get the goal type for lifting
 * that takes you from destination back to source, abstracting over the arguments
 *)
let get_arg_lift_goal_type (config : lift_config) (num_args : int) : types =
  let rec infer_goal (en : env) (b : types) (g : types) (i : int) : types =
    if i >= num_args then (* TODO, need to check if this generalizes *)
      match (kind_of_term b, kind_of_term g) with
      | (Lambda (n_b, t_b, b_b), Lambda (n_g, t_g, b_g)) when convertible en t_b t_g ->
	 let en' = push_rel (n_b, None, t_b) en in
	 let g' = unshift_local i (i - 1) (infer_goal en' b_b b_g (i + 1)) in
	 mkProd (n_b, t_b, g')
      | (Prod (n_b, t_b, b_b), Prod (n_g, t_g, b_g)) when convertible en t_b t_g ->
	 let en' = push_rel (n_b, None, t_b) en in
	 let g' = unshift_local i (i - 1) (infer_goal en' b_b b_g (i + 1)) in
	 mkProd (n_b, t_b, g')
      | _ ->
	 let diff = i - num_args in
	 let b' = shift_local (diff - 2) (i - 2) b in (* TODO num_args or i? *)
	 let g' = shift_local (diff - 1) (i - 1) g in (* TODO bounds may be wrong in here and elsewhere, unsure why this works *)
	 mkProd (Anonymous, b', g')
    else
      let (n_b, t_b, b_b) = destLambda b in
      let (n_g, t_g, b_g) = destLambda g in
      let en' = push_rel (n_b, None, t_b) en in
      mkProd (n_b, t_b, shift_local i 1 (infer_goal en' b_b b_g (i + 1)))
  in
  if config.is_concrete then
    infer_goal config.env config.f_base config.f_goal 1
  else (* TODO yet another hack, help *)
    let rec infer_goal b g =
      match (kind_of_term b, kind_of_term g) with
      | (Lambda (n_b, t_b, b_b), Lambda (_, _, b_g)) ->
         mkProd (n_b, t_b, infer_goal b_b b_g)
      | _ ->
         mkProd (Anonymous, b, g)
    in infer_goal config.f_base config.f_goal

(*
 * When abstracting over a property, add the property itself to the arguments
 * to abstract over
 *)
let get_concrete_prop (config : lift_config) (concrete : closure) : closure =
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
  match strategy.to_lift with
  | Arguments ->
     concrete
  | Property _ ->
     get_concrete_prop config concrete

(* Get abstract arguments for a function *)
let get_abstract_args config : closure =
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
  match strategy.to_lift with
  | Arguments ->
     let (env_abs, args_abs) = get_abstract_args config in
     let p = shift_by (List.length args_abs) config.f_base in
     let base_abs = specialize_using s env_abs p (Array.of_list args_abs) in
     (env_abs, List.append args_abs [base_abs])
  | Property _ ->
     let args_abs = config.args in
     let (env_p, args_p) = concrete in
     let p = mkRel (List.length args_p) in
     let base_abs = specialize_using s env_p p (Array.of_list args_abs) in
     (env_p, List.append (p :: List.tl args_abs) [base_abs])

(* Given a lifting strategy, get the lifting options for the
   particular function and arguments *)
let get_lift_opts config strategy : lifting_options =
  let concrete = get_concrete config strategy in
  let abstract = get_abstract config concrete strategy in
  match strategy.to_lift with
  | Arguments ->
     let num_to_abstract = List.length config.args in
     let goal_type = get_arg_lift_goal_type config num_to_abstract in
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
  match strategy.to_lift with
  | Arguments ->
     if is_concrete then
       List.map (shift_by opts.num_to_abstract)
     else
       List.map id
  | Property _ ->
     List.map id

(* Lift candidates with a provided abstraction strategy *)
let lift_with_strategy (config : lift_config) strategy : types list =
  let opts = get_lift_opts config strategy in
  let (env, args) = opts.concrete in
  let (env_abs, args_abs) = opts.abstract in
  let reduced_cs = reduce_all strategy.reducer env config.cs in
  let shift_concrete = shift_terms config.is_concrete strategy opts in
  let args_adj = shift_concrete args in
  let cs_adj = shift_concrete reduced_cs in
  let abstracter = strategy.abstracter in
  let bs = abstract_candidates abstracter env_abs args_adj args_abs cs_adj in
  let lambdas = wrap_candidates_in_lambdas env_abs opts.num_to_abstract bs in
  Printf.printf "%d lifted candidates\n" (List.length lambdas);
  strategy.filter env opts.goal_type lambdas

(*
 * Try to lift candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *
 * TODO clean types after generalizing w args
 *)
let lift_with_strategies (config : lift_config) : types list =
  let lift_using = lift_with_strategy config in
  let rec try_lift_using strategies =
    match strategies with
    | h :: t ->
       let lifted = lift_using h in
       if (List.length lifted) > 0 then
         lifted
       else
         try_lift_using t
    | _ ->
       []
  in try_lift_using config.strategies
