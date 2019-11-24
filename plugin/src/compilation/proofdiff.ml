(* Difference between old and new proofs *)

open Constr
open Environ
open Evd
open Proofcat
open Assumptions
open Expansion
open Evaluation
open Proofcatterms
open Reducers
open Declarations
open Utilities
open Merging
open Indutils
open Convertibility
open Stateutils

(* --- Types --- *)

(* TODO remove before merging *)
type 'a proof_diff = 'a * 'a * equal_assumptions

(* --- Kinds of proof diffs --- *)

(* TODO same *)
(* Difference between inductive proof_cats with params and leftover arguments *)
type induction_diff = (proof_cat * int * (types list)) proof_diff

(* Non-contextual difference between two proof categories *)
type proof_cat_diff = proof_cat proof_diff

(* Difference between two proof categories that have been split into cases *)
type case_diff = (proof_cat list) proof_diff

(* Difference between two goal contexts without any proof information *)
type lift_goal_diff = context_object proof_diff
type lift_goal_type_diff = (types * env) proof_diff

(* Difference between two terms given their types *)
type 'a term_diff = ('a * types) proof_diff

(* Difference between two terms given a (type, env) goal *)
type goal_type_term_diff = (types * env) term_diff

(* Difference between two terms with a goal context *)
type 'a goal_diff = (context_object * 'a) proof_diff
type goal_term_diff = types goal_diff
type goal_proof_diff = proof_cat goal_diff
type goal_case_diff = (arrow list) goal_diff

(* --- Transformations between proof diffs --- *)

(* Map a function on the old and new proofs of a diff and update assumptions *)
let map_diffs f g (o, n, assums) =
  bind
    (map_tuple_state f (o, n))
    (fun (o, n) -> bind (g assums) (fun assums -> ret (o, n, assums)))

(*
 * Retain the same goals and assumptions,
 * but update the term in a goal proof diff
 *)
let eval_with_term f g trm (d : goal_proof_diff) =
  let (goal, _) = f d in
  let env = context_env goal in
  bind
    (eval_proof env trm)
    (fun p -> g (goal, p) d)

let eval_with_old_term = 
  eval_with_term
    (fun (o, _, _) -> o)
    (fun o (_, n, assums) -> ret (o, n, assums))

let eval_with_new_term = 
  eval_with_term
    (fun (_, n, _) -> n)
    (fun n (o, _, assums) -> ret (o, n, assums))

let eval_with_terms o n d =
  bind (eval_with_new_term n d) (eval_with_old_term o)

(* --- Construction and destruction --- *)

(* Get the proof terms for a goal_diff *)
let diff_proofs ((_, term_o), (_, term_n), _) : 'a * 'a =
  (term_o, term_n)

(* Get the proof terms for a proof diff *)
let proof_terms ((_, o), (_, n), _) : types * types =
  map_tuple only_extension_as_term (o, n)

(* Auxiliary functions for merging envionrments for a diff *)
let merge_lift_diff_envs (o, n, assums) (trms : types list) =
  let (o, n) = map_tuple dest_context_term (o, n) in
  let ((goal_o, env_o), (goal_n, env_n), assums) = (o, n, assums) in
  let (env, os, ns) = merge_term_lists (env_o, env_n) (goal_o :: trms, [goal_n]) assums in
  let goal_n = List.hd ns in
  let goal_o = List.hd os in
  (env, (goal_o, goal_n, assums), List.tl os)

(* Get the goal types for a lift goal diff *)
let goal_types (o, n, assums) : types * types =
  let (typ_o, _), (typ_n, _) = map_tuple dest_context_term (o, n) in
  (typ_o, typ_n)

(* --- Reduction and Simplification --- *)

(* Reduce the terms inside of a goal_proof_diff *)
let reduce_diff (r : reducer) d : evar_map -> goal_proof_diff state =
  let (o, n) = proof_terms d in
  let ((goal_o, _), (goal_n, _), assums) = d in
  let env_o = context_env goal_o in
  let env_n = context_env goal_n in
  bind
    (fun sigma -> r env_o sigma o)
    (fun o ->
      bind
	(fun sigma -> r env_n sigma n)
	(fun n -> eval_with_terms o n d))

(* Given a difference in proofs, trim down any casts and get the terms *)
let rec reduce_casts terms =
  match map_tuple kind terms with
  | (Cast (t, _, _), _) ->
     reduce_casts (t, snd terms)
  | (_, Cast (t, _, _)) ->
     reduce_casts (fst terms, t)
  | _ ->
     terms

(*
 * Given a difference in proofs, substitute the head let ins
 * Fail silently
 *)
let reduce_letin envs terms =
  try
    if isLetIn (fst terms) || isLetIn (snd terms) then
      bind
	(fun sigma -> reduce_whd_if_let_in (fst envs) sigma (fst terms))
	(fun o' ->
	  bind
	    (fun sigma -> reduce_whd_if_let_in (snd envs) sigma (snd terms))
	    (fun n' ->
              ret (o', n')))
    else
      ret terms
  with _ ->
    ret terms

(* Given a term, trim off the IH, assuming it's an application *)
let trim_ih (trm : types) : types =
  assert (isApp trm);
  let (f, args) = destApp trm in
  let args_trim = Array.sub args 0 ((Array.length args) - 1) in
  (* TODO Talia: this looks like it's making a silly assumption about
     where the IH is located. *)
  mkApp (f, args_trim)

(* Given a diff, trim off the IHs, assuming the terms are applications *)
let reduce_trim_ihs terms =
  map_tuple trim_ih terms

(* --- Assumptions --- *)

(*
 * Update the assumptions in a case of the inductive proof
 * Shift by the number of morphisms in the case,
 * assuming they are equal when they are convertible
 *)
let update_case_assums assums c_envs c_goals =
  fold_left2_state
    (fun assums envs goals ->
      let env, goal_o, goal_n = merge_terms envs goals assums in
      branch_state
	(fun (o, n) sigma -> convertible env sigma o n)
	(fun _ -> ret (assume_local_equal assums))
	(fun _ -> ret (shift_assumptions assums))
	(goal_o, goal_n))
    assums
    (fold_tuple List.combine c_envs)
    (fold_tuple List.combine c_goals)

(* --- Questions about differences between proofs --- *)

let constructor_types (env : env) (mutind_body : mutual_inductive_body) =
  let i = Array.get mutind_body.mind_packets 0 in
  Array.to_list i.mind_nf_lc

let changed_constrs env ind_o ind_n =
  let cs_o = constructor_types env ind_o in
  let cs_n = constructor_types env ind_n in
  let cs = List.map2 (fun o n -> (o, n)) cs_o cs_n in
  List.filter (fun (o, n) -> not (equal o n)) cs

(*
 * Check if two types are inductive types with the same shape
 *
 * Fail if there are any assumptions in d
 * For now, only allow one constructor to change
 * The rest must be equal
 *)
let same_shape (env : env) (o, n, assums) : bool =
  assert (num_assumptions assums = 0);
  match map_tuple kind (o, n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let ind_o = lookup_mind i_o env in
     let ind_n = lookup_mind i_n env in
     if num_constrs ind_o = num_constrs ind_n then
       let neqs = changed_constrs env ind_o ind_n in
       List.length neqs = 1
     else
       false
  | _ ->
     false

(*
 * Given two inductive types with the same shape,
 * return the difference between them
 *
 * Fail if they are not the same shape
 * For now, assume only one constructor changes
 *
 * TODO move to differencing component
 * TODO port from cats
 *)
let ind_type_diff (env : env) (o, n, assums) : types proof_diff =
  assert (same_shape env (o, n, assums));
  let (Ind ((i_o, _), _), Ind ((i_n, _), _)) = map_tuple kind (o, n) in
  let ind_o = lookup_mind i_o env in
  let ind_n = lookup_mind i_n env in
  let neqs = changed_constrs env ind_o ind_n in
  let rec remove_conclusion c =
    match kind c with
    | Prod (n, t, b) ->
       if isProd b then
         mkProd (n, t, remove_conclusion b)
       else
         t
    | _ ->
       c
  in
  let (constr_o, constr_n) = map_tuple remove_conclusion (List.hd neqs) in
  constr_o, constr_n, (no_assumptions)

(*
 * Check whether c1 and c2 induct over the same hypothesis
 *
 * For now, only handles cases when the induction principle is the first
 * term in the application. To generalize this, we need to somehow zoom in
 * to places where the induction principle occurs if we have
 * two proofs like (f x y z (ind .... )) (f x y z (ind ..... )).
 * So this is a good benchmark case and we can extend this after.
 *)
let induct_over_same_h eq assums envs terms =
  let (term_o, term_n) = terms in
  if isApp term_o && isApp term_n then
    let (f_o, _) = destApp term_o in
    let (f_n, _) = destApp term_n in
    match map_tuple kind (f_o, f_n) with
    | (Const k_o, Const k_n) ->
       let ind_o_opt = inductive_of_elim (fst envs) k_o in
       let ind_n_opt = inductive_of_elim (snd envs) k_n in
       if Option.has_some ind_o_opt && Option.has_some ind_n_opt then
         (* should be checking that the types are the same, too *)
         let (env, os, ns) = merge_term_lists envs ([f_o], [f_n]) assums in
         eq env (List.hd os) (List.hd ns)
       else
         ret false
    | _ ->
       ret false
  else
    ret false

