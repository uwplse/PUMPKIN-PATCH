open Proofcat
open Proofdiff
open Expansion
open Assumptions
open Coqterms
open Evaluation
open Term
open Utilities

(* --- Zooming --- *)

type 'a intro_strategy = 'a proof_diff -> 'a proof_diff option

type 'a zoomer =
  'a expansion_strategy ->
  'a intro_strategy ->
  'a proof_diff ->
  'a proof_diff option

(* --- Introduction strategies --- *)

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
  let c1 = old_proof d in
  let c2 = new_proof d in
  let assums = assumptions d in
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    None
  else
    Some
      (with_old_proof
         (remove_first_n n c1)
         (with_new_proof
            (remove_first_n n c2)
            (with_assumptions (assume_local_n_equal n assums) d)))

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
  let c1 = old_proof d in
  let c2 = new_proof d in
  let assums = assumptions d in
  if (List.length (morphisms c1) <= n) || (List.length (morphisms c2) <= n) then
    None
  else
    Some
      (with_old_proof
         (remove_first_n n c1)
         (with_new_proof
            (remove_first_n n c2)
            (with_assumptions (shift_assumptions_by n assums) d)))

(*
 * Introduce an element of c1 and c2 if possible
 * Remove it from the premise of c1 and c2
 * Shift the assumptions
 *)
let intro = intro_n 1

(* --- Zoomers and using zoomers --- *)

(* Zoom *)
let zoom expander (introducer : 'a intro_strategy) (d : 'a proof_diff) =
  let a1 = old_proof d in
  let a2 = new_proof d in
  let d = with_old_proof (expander a1) (with_new_proof (expander a2) d) in
  introducer d

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

(* TODO move expand below into actual expansion *)
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
