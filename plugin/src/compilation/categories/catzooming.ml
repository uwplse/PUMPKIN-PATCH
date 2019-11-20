open Stateutils
open Proofcat
open Environ
open Proofdiff
open Proofcatterms
open Expansion
open Assumptions
open Candidates
open Constr
open Debruijn
open Evd

(* --- Zooming --- *)

type search_function = proof_cat_diff -> evar_map -> candidates state
type 'a intro_strategy = 'a proof_diff -> evar_map -> ('a proof_diff option) state

type 'a zoomer =
  'a expansion_strategy ->
  'a intro_strategy ->
  'a proof_diff ->
  evar_map ->
  ('a proof_diff option) state

(* --- Introduction strategies --- *)

(* Remove the initial object of c *)
let remove_initial (c : proof_cat) =
  let i = initial c in
  let ms = morphisms c in
  bind
    (bind (objects c) (all_objects_except i))
    (fun os' ->
      bind
        (partition_state (map_source (objects_not_equal i)) ms)
	(fun (ms', ims) ->
	  let (_, _, i') = List.hd ims in
	  make_category os' ms' (Some i') (terminal_opt c)))

(* Remove the first n contexts *)
let rec remove_first_n (n : int) (c : proof_cat) =
  if n = 0 then
    ret c
  else
    bind (remove_initial c) (remove_first_n (n - 1))

(*
 * Introduce n common elements of c1 and c2 if possible
 * Remove those elements from the premise of c1 and c2
 * Add them to assums
 *)
let intro_common_n n (c1, c2, assums) sigma =
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    sigma, None
  else
    let sigma, c1' = remove_first_n n c1 sigma in
    let sigma, c2' = remove_first_n n c2 sigma in
    sigma, Some (c1', c2', assume_local_n_equal n assums)

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
let intro_n n (c1, c2, assums) sigma =
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    sigma, None
  else
    let sigma, c1' = remove_first_n n c1 sigma in
    let sigma, c2' = remove_first_n n c2 sigma in
    sigma, Some (c1', c2', shift_assumptions_by n assums)

(*
 * Introduce an element of c1 and c2 if possible
 * Remove it from the premise of c1 and c2
 * Shift the assumptions
 *)
let intro = intro_n 1

(* --- Zoomers and using zoomers --- *)
    
(* Zoom *)
let zoom expander (introducer : 'a intro_strategy) (a1, a2, assums) =
  bind
    (expander a1)
    (fun o -> bind (expander a2) (fun n -> introducer (o, n, assums)))

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
  bind
    (zoom expander introducer d)
    (fun zoomed ->
      if not (Option.has_some zoomed) then
	ret a
      else
	f (Option.get zoomed))

(* Default zoom for recursive search *)
let zoom_search f ((_, o), (_, n), assums) =
  zoom_map
    f
    give_up
    expand_terminal
    intro_common
    (o, n, assums)

(* TODO temproary for refactor *)
let temp_to_diff assums envs terms goals sigma =
  let sigma, o = Evaluation.eval_proof (fst envs) (fst terms) sigma in
  let sigma, n = Evaluation.eval_proof (snd envs) (snd terms) sigma in
  let goal_o = Proofcat.Context (Proofcat.Term (fst goals, fst envs), Utilities.fid ()) in
  let goal_n = Proofcat.Context (Proofcat.Term (snd goals, snd envs), Utilities.fid ()) in
  let d = ((goal_o, o), (goal_n, n), assums) in
  sigma, d
    
(* Zoom in, search, and wrap the result in a lambda from binding (n : t)  *)
let zoom_wrap_lambda f n t assums envs terms goals sigma =
  let sigma, d = temp_to_diff assums envs terms goals sigma in
  zoom_search
    (fun d -> bind (f d) (map_state (fun c -> ret (mkLambda (n, t, c)))))
    d
    sigma

(* Zoom in, search, and wrap the result in a prod from binding (n : t) *)
let zoom_wrap_prod f n t (d : goal_proof_diff) =
  zoom_search
    (fun d -> bind (f d) (map_state (fun c -> ret (mkProd (n, t, c)))))
    d

(* Zoom in, search, and unshift the result *)
let zoom_unshift f assums envs terms goals sigma =
  let sigma, d = temp_to_diff assums envs terms goals sigma in
  zoom_search
    (fun d -> bind (f d) (map_state (fun t -> ret (unshift t))))
    d
    sigma
