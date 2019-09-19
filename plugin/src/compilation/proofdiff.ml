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

(* Destruct the contexts in a diff and return a new diff *)
let dest_goals ((goal_o, a_o), (goal_n, a_n), assums) =
  (dest_context_term goal_o, a_o), (dest_context_term goal_n, a_n), assums

(* Destruct the contexts in a diff and return a new diff *)
let dest_lift_goals (o, n, assums) : lift_goal_type_diff =
  dest_context_term o, dest_context_term n, assums

(* Destruct a case diff into a list of diffs, one for each case *)
let dest_cases (os, ns, assums) : proof_cat_diff list =
  List.map2 (fun o n -> o, n, assums) os ns

(* Expand constructors in a proof_cat_diff *)
let expand_constrs (o, n, assums) =
  bind
    (expand_constr o)
    (fun o -> bind (expand_constr n) (fun n -> ret (o, n, assums)))

(* --- Construction and destruction --- *)

(* Get the proof terms for a goal_diff *)
let diff_proofs ((_, term_o), (_, term_n), _) : 'a * 'a =
  (term_o, term_n)

(* Get the proof terms for a proof diff *)
let proof_terms ((_, o), (_, n), _) : types * types =
  map_tuple only_extension_as_term (o, n)

(* Auxiliary functions for merging envionrments for a diff *)
(* TODO directionality swapped; either fix in merge or here *)
let merge_lift_diff_closures ((goal_o, env_o), (goal_n, env_n), assums) trms =
  merge_term_lists (env_n, env_o) ([goal_n], goal_o :: trms) assums

(* TODO same for directions *)
let merge_lift_diff_envs (o, n, assums) (trms : types list) =
  let (o, n, assums) = dest_lift_goals (o, n, assums) in
  let (env, ns, os) = merge_lift_diff_closures (o, n, assums) trms in
  let goal_n = List.hd ns in
  let goal_o = List.hd os in
  (env, (goal_o, goal_n, assums), List.tl os)

(* TODO same *)
let merge_diff_closures (o, n, assums) trms =
  let ((goal_o, env_o), term_o) = o in
  let ((goal_n, env_n), term_n) = n in
  merge_term_lists
    (env_n, env_o)
    ([goal_n; term_n], List.append [goal_o; term_o] trms)
    assums

(* Get the goal types for a lift goal diff *)
let goal_types (o, n, assums) : types * types =
  let ((goal_o, _), (goal_n, _), _) = dest_lift_goals (o, n, assums) in
  (goal_o, goal_n)

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
let rec reduce_casts (d : goal_proof_diff) =
  match map_tuple kind (proof_terms d) with
  | (Cast (t, _, _), _) ->
     bind (eval_with_old_term t d) reduce_casts
  | (_, Cast (t, _, _)) ->
     bind (eval_with_new_term t d) reduce_casts
  | _ ->
     ret d

(*
 * Given a difference in proofs, substitute the head let ins
 * Fail silently
 *)
let reduce_letin (d : goal_proof_diff) =
  let (o, n) = proof_terms d in
  try
    if isLetIn o || isLetIn n then
      let (((_, env_o), _), ((_, env_n), _), _) = dest_goals d in
      bind
	(fun sigma -> reduce_whd_if_let_in env_o sigma o)
	(fun o' ->
	  bind
	    (fun sigma -> reduce_whd_if_let_in env_n sigma n)
	    (fun n' -> eval_with_terms o' n' d))
    else
      ret d
  with _ ->
    ret d

(* Given a term, trim off the IH, assuming it's an application *)
let trim_ih (trm : types) : types =
  assert (isApp trm);
  let (f, args) = destApp trm in
  let args_trim = Array.sub args 0 ((Array.length args) - 1) in
  mkApp (f, args_trim)

(* Given a diff, trim off the IHs, assuming the terms are applications *)
let reduce_trim_ihs (d : goal_proof_diff) =
  let (old_term, new_term) = map_tuple trim_ih (proof_terms d) in
  eval_with_terms old_term new_term d

(* --- Assumptions --- *)

(*
 * Update the assumptions in a case of the inductive proof
 * Shift by the number of morphisms in the case,
 * assuming they are equal when they are convertible
 *)
let update_case_assums (ms_o, ms_n, assums) =
  fold_left_state
    (fun assums (dst_o, dst_n) ->
      let d = dst_o, dst_n, assums in
      let (env, d_goal, _) = merge_lift_diff_envs d [] in
      branch_state
	(fun (o, n, _) sigma -> convertible env sigma o n)
	(fun _ -> ret (assume_local_equal assums))
	(fun _ -> ret (shift_assumptions assums))
	d_goal)
    assums
    (List.fold_right2
       (fun dst_o dst_n combined -> (dst_o, dst_n) :: combined)
       (conclusions (all_but_last ms_o))
       (conclusions (all_but_last ms_n))
       [])

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
let induct_over_same_h eq (d : goal_proof_diff) : bool =
  let ((_, o), (_, n), _) = dest_goals d in
  let trm1 = only_extension_as_term o in
  let trm2 = only_extension_as_term n in
  if (isApp trm1) && (isApp trm2) then
    let (f1, _) = destApp trm1 in
    let (f2, _) = destApp trm2 in
    match (kind f1, kind f2) with
    | (Const k1, Const k2) ->
       let ind1_opt = inductive_of_elim (context_env (terminal o)) k1 in
       let ind2_opt = inductive_of_elim (context_env (terminal n)) k2 in
       if Option.has_some ind1_opt && Option.has_some ind2_opt then
         (* should be checking that the types are the same, too *)
         eq f1 f2
       else
         false
    | _ ->
       false
  else
    false

(* Get the number of bindings that are not common to both proofs in d *)
let num_new_bindings (f : 'a -> env) (o, n, assums) =
  num_assumptions (complement_assumptions assums (f o))
