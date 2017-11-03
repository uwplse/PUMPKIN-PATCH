(* Difference between old and new proofs *)

open Term
open Environ
open Proofcat
open Assumptions
open Expansion
open Coqterms
open Evaluation
open Utilities
open Proofcatterms
open Substitution
open Reducers
open Declarations
open Collections
open Printing

(* --- Types --- *)

type 'a proof_diff = 'a * 'a * equal_assumptions
type 'a intro_strategy = 'a proof_diff -> 'a proof_diff option
type 'a zoomer =
  'a expansion_strategy ->
  'a intro_strategy ->
  'a proof_diff ->
  'a proof_diff option

(* Construct a proof_diff *)
let difference a1 a2 assums =
  (a1, a2, assums)

(* Get the assumptions from a proof_diff *)
let assumptions (a1, a2, assums) =
  assums

(* Get the old proof from a proof_diff *)
let old_proof (a1, a2, assums) =
  a1

(* Get the new proof from a proof_diff *)
let new_proof (a1, a2, assums) =
  a2

(* Change the assumptions of a proof_diff *)
let with_assumptions assums (a1, a2, _) =
  (a1, a2, assums)

(* Change the old proof of a proof_diff *)
let with_old_proof a1 (_, a2, assums) =
  (a1, a2, assums)

(* Change the new proof of a proof_diff *)
let with_new_proof a2 (a1, _, assums) =
  (a1, a2, assums)

(* --- Kinds of proof diffs --- *)

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
let map_diffs f g (d : 'a proof_diff) : 'b proof_diff =
  difference (f (old_proof d)) (f (new_proof d)) (g (assumptions d))

(*
 * Add extra information to the old and new proofs, respectively
 *)
let add_to_diff (d : 'a proof_diff) (b1 : 'b) (b2 : 'b) : ('a * 'b) proof_diff =
  let a1 = old_proof d in
  let a2 = new_proof d in
  difference (a1, b1) (a2, b2) (assumptions d)

(*
 * Reverse a diff, so that the new proof is the old proof and the
 * old proof is the new proof.
 *)
let reverse (d : 'a proof_diff) : 'a proof_diff =
  difference (new_proof d) (old_proof d) (reverse_assumptions (assumptions d))

(*
 * Swap the goals in a goal diff
 *)
let swap_goals (d : 'a goal_diff) : 'a goal_diff =
  let (g_o, o) = old_proof d in
  let (g_n, n) = new_proof d in
  difference (g_o, n) (g_n, o) (assumptions d)

(*
 * Given a difference in proof categories, get the contexts for the
 * types of the conclusions (terminal objects), and return
 * a new difference that includes these as goal types
 *)
let add_goals (d : proof_cat_diff) : goal_proof_diff =
  let c1 = old_proof d in
  let c2 = new_proof d in
  let t1 = terminal c1 in
  let t2 = terminal c2 in
  difference (t1, c1) (t2, c2) (assumptions d)

(*
 * Erase the goals from a goal diff
 *)
let erase_goals (d : 'a goal_diff) : 'a proof_diff =
  let (_, o) = old_proof d in
  let (_, n) = new_proof d in
  difference o n (assumptions d)

(* Erase the proof terms, however they are represented, from a goal_diff *)
let erase_proofs (d : 'a goal_diff) : lift_goal_diff =
  let (c_o, _) = old_proof d in
  let (c_n, _) = new_proof d in
  difference c_o c_n (assumptions d)

(* Convert a difference in proof categories to a difference in terms *)
let proof_to_term (d : goal_proof_diff) : goal_term_diff =
  let (old_goal, o) = old_proof d in
  let (new_goal, n) = new_proof d in
  let old_term = only_extension_as_term o in
  let new_term = only_extension_as_term n in
  difference (old_goal, old_term) (new_goal, new_term) (assumptions d)

(*
 * Retain the same goals and assumptions,
 * but update the term in a goal proof diff
 *)
let eval_with_term f g trm (d : goal_proof_diff) : goal_proof_diff =
  let (goal, _) = f d in
  let env = context_env goal in
  g (goal, eval_proof env trm) d

let eval_with_old_term = eval_with_term old_proof with_old_proof

let eval_with_new_term = eval_with_term new_proof with_new_proof

let eval_with_terms o n d =
  eval_with_old_term o (eval_with_new_term n d)

(* Destruct the contexts in a diff and return a new diff *)
let dest_goals (d : 'a goal_diff) =
  let (old_goal, old_a) = old_proof d in
  let (new_goal, new_a) = new_proof d in
  difference
    (dest_context_term old_goal, old_a)
    (dest_context_term new_goal, new_a)
    (assumptions d)

(* Destruct the contexts in a diff and return a new diff *)
let dest_lift_goals (d : lift_goal_diff) : lift_goal_type_diff =
  difference
    (dest_context_term (old_proof d))
    (dest_context_term (new_proof d))
    (assumptions d)

(* Destruct a case diff into a list of diffs, one for each case *)
let dest_cases (d : case_diff) : proof_cat_diff list =
  let assums = assumptions d in
  let os = old_proof d in
  let ns = new_proof d in
  List.map2 (fun o n -> difference o n assums) os ns

(* --- Construction and destruction --- *)

(* Get the proof terms for a goal_diff *)
let diff_proofs (d : 'a goal_diff) : 'a * 'a =
  let (_, old_term) = old_proof d in
  let (_, new_term) = new_proof d in
  (old_term, new_term)

(* Get the proof terms for a proof diff *)
let proof_terms (d : goal_proof_diff) : types * types =
  diff_proofs (proof_to_term d)

(* Auxiliary functions for merging envionrments for a diff *)
let merge_lift_diff_closures (d : lift_goal_type_diff) (trms : types list) =
  let assums = assumptions d in
  let (old_goal_type, old_goal_env) = old_proof d in
  let (new_goal_type, new_goal_env) = new_proof d in
  merge_closures
    (new_goal_env, [new_goal_type])
    (old_goal_env, old_goal_type :: trms)
    assums

let merge_diff_closures (d : goal_type_term_diff) (trms : types list) =
  let assums = assumptions d in
  let ((old_goal_type, old_goal_env), old_term) = old_proof d in
  let ((new_goal_type, new_goal_env), new_term) = new_proof d in
  merge_closures
    (new_goal_env, [new_goal_type; new_term])
    (old_goal_env, List.append [old_goal_type; old_term] trms)
    assums

(* Get the reduced proof terms for a proof diff *)
let reduced_proof_terms (r : reducer) (d : goal_proof_diff) : env * types * types =
  let (env, ns, os) = merge_diff_closures (dest_goals (proof_to_term d)) [] in
  let [new_goal_type; new_term] = ns in
  let [old_goal_type; old_term] = os in
  (env, r env old_term, r env new_term)

(* Get the goal types for a lift goal diff *)
let goal_types (d : lift_goal_diff) : types * types =
  let d_type_env = dest_lift_goals d in
  let (old_goal_type, _) = old_proof d_type_env in
  let (new_goal_type, _) = new_proof d_type_env in
  (old_goal_type, new_goal_type)

(* --- Reduction --- *)

(* Reduce the terms inside of a goal_proof_diff *)
let reduce_diff (r : reducer) (d : goal_proof_diff) : goal_proof_diff =
  let (o, n) = proof_terms d in
  let (goal_o, _) = old_proof d in
  let (goal_n, _) = new_proof d in
  let env_o = context_env goal_o in
  let env_n = context_env goal_n in
  eval_with_terms (r env_o o) (r env_n n) d

(* --- Questions about differences between proofs --- *)

let constructor_types (env : env) (mutind_body : mutual_inductive_body) =
  let i = Array.get mutind_body.mind_packets 0 in
  Array.to_list i.mind_nf_lc

let changed_constrs env ind_o ind_n =
  let cs_o = constructor_types env ind_o in
  let cs_n = constructor_types env ind_n in
  let cs = List.map2 (fun o n -> (o, n)) cs_o cs_n in
  List.filter (fun (o, n) -> not (eq_constr o n)) cs

(*
 * Check if two types are inductive types with the same shape
 *
 * Fail if there are any assumptions in d
 * For now, only allow one constructor to change
 * The rest must be eq_constr
 *)
let same_shape (env : env) (d : types proof_diff) : bool =
  assert (num_assumptions (assumptions d) = 0);
  let o = old_proof d in
  let n = new_proof d in
  match map_tuple kind_of_term (o, n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let ind_o = lookup_mutind_body i_o env in
     let ind_n = lookup_mutind_body i_n env in
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
 *)
let ind_type_diff (env : env) (d : types proof_diff) : types proof_diff =
  assert (same_shape env d);
  let o = old_proof d in
  let n = new_proof d in
  let (Ind ((i_o, _), _), Ind ((i_n, _), _)) = map_tuple kind_of_term (o, n) in
  let ind_o = lookup_mutind_body i_o env in
  let ind_n = lookup_mutind_body i_n env in
  let neqs = changed_constrs env ind_o ind_n in
  let rec remove_conclusion c =
    match kind_of_term c with
    | Prod (n, t, b) ->
       if isProd b then
         mkProd (n, t, remove_conclusion b)
       else
         t
    | _ ->
       c
  in
  let (constr_o, constr_n) = map_tuple remove_conclusion (List.hd neqs) in
  difference constr_o constr_n (no_assumptions)

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
  let d = dest_goals d in
  let (_, o) = old_proof d in
  let (_, n) = new_proof d in
  let trm1 = only_extension_as_term o in
  let trm2 = only_extension_as_term n in
  if (isApp trm1) && (isApp trm2) then
    let (f1, _) = destApp trm1 in
    let (f2, _) = destApp trm2 in
    match (kind_of_term f1, kind_of_term f2) with
    | (Const k1, Const k2) ->
       let ind1_opt = inductive_of_elim (context_env (terminal o)) k1 in
       let ind2_opt = inductive_of_elim (context_env (terminal n)) k2 in
       if Option.has_some ind1_opt && Option.has_some ind2_opt then
           let ind1 = Option.get ind1_opt in
           let ind2 = Option.get ind2_opt in
           eq f1 f2
       else
         false
    | _ ->
       false
  else
    false

(* Get the number of bindings that are not common to both proofs in d *)
let num_new_bindings (f : 'a -> env) (d : 'a proof_diff) =
  let assums = assumptions d in
  num_assumptions (complement_assumptions assums (f (old_proof d)))

(* --- Zooming --- *)

(* Remove the initial object of c *)
let remove_initial (c : proof_cat) : proof_cat =
  let i = initial c in
  let os = objects c in
  let ms = morphisms c in
  let os' = all_objects_except i (objects c) in
  let (ms', ims) = List.partition (map_source (objects_not_equal i)) ms in
  let (_, _, i') = List.hd ims in
  make_category os' ms' (Some i') (terminal_opt c)

(* Remove the first n contexts *)
let rec remove_first_n (n : int) (c : proof_cat) : proof_cat =
  if n = 0 then
    c
  else
    remove_first_n (n - 1) (remove_initial c)

(*
 * Introduce n common elements of c1 and c2 if possible
 * Remove those elements from the premise of c1 and c2
 * Add them to assums
 *)
let intro_common_n n (d : proof_cat_diff) : proof_cat_diff option =
  let (c1, c2, assums) = d in
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    None
  else
    let c1' = remove_first_n n c1 in
    let c2' = remove_first_n n c2 in
    Some (c1', c2', assume_local_n_equal n assums)

(*
 * Introduce a common element of c1 and c2 if possible
 * Remove that element from the premise of c1 and c2
 * Add it to assums
 *)
let intro_common = intro_common_n 1

(*
 * Introduce n elements of c1 and c2 if possible
 * Remove those elements from the premise of c1 and c2
 * Shift the assumptions
 *)
let intro_n n (d : proof_cat_diff) : proof_cat_diff option =
  let (c1, c2, assums) = d in
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    None
  else
    let c1' = remove_first_n n c1 in
    let c2' = remove_first_n n c2 in
    Some (c1', c2', shift_assumptions_by n assums)

(*
 * Introduce an element of c1 and c2 if possible
 * Remove it from the premise of c1 and c2
 * Shift the assumptions
 *)
let intro = intro_n 1

(* Zoom *)
let zoom expander introducer d =
  let (a1, a2, assums) = d in
  introducer (expander a1, expander a2, assums)

(*
 * Zoom
 * If it was successful, apply f to the result
 * Otherwise, default to a
 *
 * Eventually, we may want to make this a tail call, since
 * the function is often a recursor. Not sure if this will
 * help with performance given that it is mutual recursion.
 *)
let zoom_map f a expander introducer d =
  let zoomed = zoom expander introducer d in
  if not (Option.has_some zoomed) then
    a
  else
    f (Option.get zoomed)

(*
 * Expand the application of a constant function
 *)
let expand_const_application env (c, u) (f, args) default =
  match inductive_of_elim env (c, u) with
  | Some mutind ->
     let mutind_body = lookup_mutind_body mutind env in
     let f_c = eval_proof env f in
     let f_exp = expand_inductive_params mutind_body.mind_nparams f_c in
     eval_induction mutind_body f_exp args
  | None ->
     (eval_proof env (mkApp (f, args)), 0, default)

(*
 * Expand the application of a fuction
 *
 * This will not work yet when induction shows up later in the proof
 * We should make a benchmark for this and extend as needed
 *)
let expand_application_term env trm default =
  let (f, args) = destApp trm in
  match kind_of_term f with
  | Const (c, u) ->
     expand_const_application env (c, u) (f, args) default
  | _ ->
     let exp = expand_term eval_theorem (Context (Term (trm, env), fid ())) in
     (exp, 0, default)

(*
 * Expand an application arrow
 *
 * This assumes it's the only arrow in c
 * Otherwise, there is an error
 * Like the above, this will not work yet when induction is later in the proof
 *)
let expand_application (c, n, l) : proof_cat * int * (types list) =
  map_ext
    (fun e ->
      match e with
      | LazyBinding (trm, env) -> expand_application_term env trm l
      | _ -> assert false)
    (only_arrow c)

(* Zoom over two inductive proofs that induct over the same hypothesis *)
let zoom_same_hypos = zoom expand_application (fun d -> Some d)
