open Environ
open Term
open Abstracters
open Candidates
open Coqterms
open Debruijn
open Collections
open Searchopts
open Reducers

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

(* --- Fixpoints --- *)

(*
 * Abstract a term by a function for a fixpoint
 *)
let rec configure_fixpoint_case strategies (env : env) (c : types) (g : types) : abstraction_config =
  match (kind_of_term c, kind_of_term g) with
  | (Lambda (n, t, cb), Prod (_, tb, gb)) when isLambda cb && isProd gb ->
     configure_fixpoint_case strategies (push_rel (n, None, t) env) cb gb
  | (Lambda (_, _, _), Prod (_, gt, gtg)) when isApp gt && isApp gtg ->
     let (_, _, ctb) = destProd (infer_type env c) in
     if isApp ctb then
       let (f_base, _) = destApp (unshift ctb) in
       let f_goal = f_base in
       let args_base = [gt] in
       let args_goal = [unshift gtg] in
       let cs = [c] in
       {env; args_base; args_goal; cs; f_base; f_goal; strategies}
     else
       failwith "Cannot infer property to generalize"
  | _ ->
     failwith "Goal is inconsistent with term to generalize"

(*
 * Get goals for abstraction by a function for a change in fixpoint cases
 * Take an environment, a list of differences between those cases,
 * and a list of candidates
 *)
let configure_fixpoint_cases env (diffs : types list) (cs : candidates) =
  flat_map
    (fun c ->
      List.map
        (configure_fixpoint_case reduce_strategies_prop env c)
        diffs)
    cs

(* --- Cut Lemmas --- *)

(*
 * Get the arguments for abstraction by arguments
 * Also a workaround
 *
 * TODO why is this here?
 * Figure out what to do with this
 *)
let rec get_lifting_goal_args pi (app : types) : types =
  match kind_of_term app with
  | Lambda (n, t, b) ->
     mkProd (n, t, get_lifting_goal_args (pi + 1) b)
  | App (f, args) ->
     mkApp (mkRel pi, args)
  | _ ->
     failwith "Cannot infer goals for generalizing arguments"

(* Configure abstraction over arguments when cutting by a cut lemma *)
let configure_cut_args env (cut : cut_lemma) (cs : candidates) =
  let cs = filter_consistent_cut env cut cs in
  let rec configure en g : abstraction_config =
    match kind_of_term g with
    | Prod (n, t, b) ->
       configure (push_rel (n, None, t) en) b
    | App (lemma, args) ->
       let ct = infer_type en g in
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
       let (f_base, f_goal) = get_lemma_functions (infer_type en lemma) in
       let args_base = Array.to_list args in
       let args_goal = args_base in
       let env = en in
       let strategies = no_reduce_strategies in
       {env; args_base; args_goal; cs; f_base; f_goal; strategies}
  in
  let (_, _, b) = destLambda (get_app cut) in
  let g = reduce_remove_identities env (get_lifting_goal_args 1 b) in
  let env_cut = push_rel (Anonymous, None, get_lemma cut) env in
  if List.length cs > 0 then
    configure env_cut g
  else
    failwith "No candidates are consistent with the cut lemma type"
