(* --- Abstraction Component --- *)

open Proofcatterms
open Abstracters
open Abstractionconfig
open Environ
open Evd
open Constr
open Debruijn
open Utilities
open Reducers
open Specialization
open Candidates
open Proofdiff
open Searchopts
open Cutlemma
open Filters
open Zooming
open Convertibility
open Contextutils
open Merging
open Apputils

(* --- TODO for refactoring without breaking things --- *)

(*
 * Infer the type of trm in env
 * Note: This does not yet use good evar map hygeine; will fix that
 * during the refactor.
 *)
let infer_type (env : env) (evd : evar_map) (trm : types) : types =
  let jmt = Typeops.infer env trm in
  j_type jmt
               
(* --- End TODO --- *)

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
let generalize (env : env) (evd : evar_map) (num_to_abstract : int) (cs : candidates) : candidates =
  snd
    (List.fold_right
       (fun _ (en, l) ->
         let typ = unshift (infer_type en evd (mkRel 1)) in
         let env_pop = Environ.pop_rel_context 1 en in
         (env_pop, List.map (fun b -> mkLambda (Names.Name.Anonymous, typ, b)) l))
       (range 1 (num_to_abstract + 1))
       (env, cs))

(*
 * Get goals for abstraction by a function
 * TODO explain
 * TODO same concern as below *)
let get_prop_abstract_goal_type (config : abstraction_config) =
  let env = config.env in
  let prop = mkRel (nb_rel env) in
  let base = mkApp (prop, Array.of_list config.args_base) in
  let goal = mkApp (prop, Array.of_list config.args_goal) in
  let goal_type_env = mkProd (Names.Name.Anonymous, base, shift goal) in
  reconstruct_product env goal_type_env

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
let get_arg_abstract_goal_type (config : abstraction_config) : types =
  let rec infer_goal (b : types) (g : types) : types =
    match map_tuple kind (b, g) with
    | (Lambda (n_b, t_b, b_b), Lambda (_, _, b_g)) ->
       mkProd (n_b, t_b, infer_goal b_b b_g)
    | (Prod (n_b, t_b, b_b), Prod (_, _, b_g)) ->
       mkProd (n_b, t_b, infer_goal b_b b_g)
    | _ ->
       mkProd (Names.Name.Anonymous, b, shift g)
  in infer_goal config.f_base config.f_goal

(*
 * When abstracting over a property, add the property itself to the arguments
 * to abstract over
 *)
let get_concrete_prop (config : abstraction_config) (concrete : closure) : closure =
  let (env, args) = concrete in
  let p = config.f_base in
  (env, p :: (List.tl args))

(* Get the concrete environment and arguments to abstract *)
let get_concrete config strategy : closure =
  let env = config.env in
  let evd = config.evd in
  let args = config.args_base in
  let s = reducer_to_specializer reduce_term in
  let base = specialize_using s env evd config.f_base (Array.of_list args) in
  let concrete = (env, List.append args [base]) in
  match kind_of_abstraction strategy with
  | Arguments ->
     concrete
  | Property ->
     get_concrete_prop config concrete

(* Get abstract arguments for a function *)
let get_abstraction_args config : closure =
  let rec infer_args (i : int) (en : env) (g : types) : closure =
    if i = 0 then
      (en, [])
    else
      match kind g with
      | Lambda (n, t, b) ->
	 let en' = push_rel CRD.(LocalAssum(n, t)) en in
	 let (en'', b') = infer_args (i - 1) en' b in
	 (en'', (mkRel i) :: b')
      | _ ->
	 (en, [])
  in infer_args (List.length config.args_base) config.env config.f_goal

(* Get the abstract arguments that map to concrete arguments
   for a particular strategy, function, and arguments *)
let get_abstract config concrete strategy : closure =
  let s = reducer_to_specializer reduce_term in
  let evd = config.evd in
  match kind_of_abstraction strategy with
  | Arguments ->
     let (env_abs, args_abs) = get_abstraction_args config in
     let p = shift_by (List.length args_abs) config.f_base in
     let base_abs = specialize_using s env_abs evd p (Array.of_list args_abs) in
     (env_abs, List.append args_abs [base_abs])
  | Property ->
     let args_abs = config.args_base in
     let (env_p, args_p) = concrete in
     let p = mkRel (nb_rel env_p) in
     let base_abs = specialize_using s env_p evd p (Array.of_list args_abs) in
     (env_p, List.append (p :: List.tl args_abs) [base_abs])

(* Given a abstraction strategy, get the abstraction options for the
   particular function and arguments *)
(* TODO num_to_abstract uniformity *)
let get_abstraction_opts config strategy : abstraction_options =
  let concrete = get_concrete config strategy in
  let abstract = get_abstract config concrete strategy in
  match kind_of_abstraction strategy with
  | Arguments ->
     let goal_type = get_arg_abstract_goal_type config in
     let num_to_abstract = List.length config.args_base in
     { concrete; abstract; goal_type; num_to_abstract }
  | Property ->
     let goal_type = get_prop_abstract_goal_type config in
     let (env, _) = concrete in
     let num_to_abstract = nb_rel env in
     { concrete; abstract; goal_type; num_to_abstract }

(* Abstract candidates with a provided abstraction strategy *)
let abstract_with_strategy (config : abstraction_config) strategy : candidates =
  let opts = get_abstraction_opts config strategy in
  let evd = config.evd in
  let (env, args) = opts.concrete in
  let (env_abs, args_abs) = opts.abstract in
  let reduced_cs = reduce_all_using strategy env evd config.cs in
  let shift_concrete = List.map (shift_by (nb_rel env_abs - nb_rel env)) in
  let args_adj = shift_concrete args in
  let cs_adj = shift_concrete reduced_cs in
  let bs = substitute_using strategy env_abs evd args_adj args_abs cs_adj in
  let lambdas = generalize env_abs evd opts.num_to_abstract bs in
  Printf.printf "%d abstracted candidates\n" (List.length lambdas);
  filter_using strategy env evd opts.goal_type lambdas

(*
 * Try to abstract candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
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

(*
 * Try to abstract candidates in an inductive proof by their arguments
 * given the goal types of the old proof and the new proof.
 * This assumes the candidate patches are specialized (for example,
 * with type P 0 for some P) and tries to abstract them (into P n).
 *
 * If the list of candidates are empty, then this returns the empty list.
 *
 * If the goal types are not both function applications, then they are not
 * specialized, so we have nothing to abstract, and we return the original list.
 *
 * If the goal types are both specialized, then we abstract.
 *)
let try_abstract_inductive evd (d : lift_goal_diff) (cs : candidates) : candidates =
  let goals = goal_types d in
  let goals_are_apps = fold_tuple (fun t1 t2 -> isApp t1 && isApp t2) goals in
  if goals_are_apps && non_empty cs then
    let (env, d_type, cs) = merge_lift_diff_envs d cs in
    let new_goal_type = new_proof d_type in
    let old_goal_type = old_proof d_type in
    if List.for_all2 (convertible env evd) (unfold_args old_goal_type) (unfold_args new_goal_type) then
      let config = configure_args env evd d_type cs in
      let num_new_rels = num_new_bindings snd (dest_lift_goals d) in
      List.map
        (unshift_local (num_new_rels - 1) num_new_rels)
        (abstract_with_strategies config)
    else
      give_up
  else
    cs

(*
 * Abstract candidates in a case of an inductive proof.
 * Use the options to determine whether or not to abstract,
 * and how to abstract if we should abstract.
 * If there is nothing to abstract or if we cannot determine what to
 * abstract, then return the original list.
 *)
let abstract_case (opts : options) evd (d : goal_case_diff) cs : candidates =
  let d_goal = erase_proofs d in
  let old_goal = old_proof d_goal in
  let env = context_env old_goal in
  match get_change opts with
  | Kindofchange.Hypothesis (_, _) ->
     let (g_o, g_n) = map_tuple context_term (old_goal, new_proof d_goal) in
     filter_by_type (mkProd (Names.Name.Anonymous, g_n, shift g_o)) env evd cs
  | Kindofchange.InductiveType (_, _) ->
     cs
  | Kindofchange.FixpointCase ((_, _), cut) when are_cut env evd cut cs ->
     cs
  | _ ->
     try_abstract_inductive evd d_goal cs
                            
(* 
 * Replace all occurrences of the first term in the second term with Rel 1,
 * lifting de Bruijn indices as needed. The notion of term equality is modulo
 * alpha, casts, application grouping, and universes.
 *
 * By Nate Yazdani, from DEVOID.
 *)
let abstract_subterm sub term =
  (* Allocate a binding slot for the abstracted subterm *)
  let sub = Vars.lift 1 sub in
  let term = Vars.lift 1 term in
  let rec surgery (nb, sub) term =
    match eq_constr_head sub term with
    | Some args ->
      mkApp (mkRel (nb + 1), args)
    | None ->
      Constr.map_with_binders
        (fun (nb, sub) -> nb + 1, Vars.lift 1 sub)
        surgery
        (nb, sub)
        term
  in surgery (0, sub) term
