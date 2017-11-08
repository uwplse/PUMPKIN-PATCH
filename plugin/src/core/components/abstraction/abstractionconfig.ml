open Environ
open Term
open Abstracters
open Candidates
open Coqterms
open Debruijn
open Collections

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
 *)
let configure_fixpoint_cases (env : env) (diffs : types list) (cs : candidates) : abstraction_config list =
  flat_map
    (fun c ->
      List.map
        (configure_fixpoint_case reduce_strategies_prop env c)
        diffs)
    cs

