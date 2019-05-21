open Proofcat
open Environ
open Coqterms
open Proofdiff
open Proofcatterms
open Expansion
open Assumptions
open Candidates
open Constr
open Debruijn

(* --- Zooming --- *)

type search_function = proof_cat_diff -> candidates
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

(*
 * Introduce nparams parameters to an inductive diff d
  *
 * This assumes both proofs have the same number of parameters,
 * otherwise it will fail.
 *)
let intro_params nparams d =
  intro_common
    (Option.get
       (List.fold_right2
          (fun (_, e1, _) (_, e2, _) d_opt ->
            let d = Option.get d_opt in
            if extensions_equal_assums e1 e2 (assumptions d) then
              intro_common d
            else
              intro d)
          (params (old_proof d) nparams)
          (params (new_proof d) nparams)
          (Some d)))

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

(* Zoom over two inductive proofs that induct over the same hypothesis *)
let zoom_same_hypos = zoom expand_application (fun d -> Some d)

(* Default zoom for recursive search *)
let zoom_search f (d : goal_proof_diff) : candidates =
  zoom_map
    f
    give_up
    expand_terminal
    intro_common
    (erase_goals d)

(* Zoom in, search, and wrap the result in a lambda from binding (n : t)  *)
let zoom_wrap_lambda f n t (d : goal_proof_diff) : candidates =
  zoom_search
    (fun d -> List.map (fun c -> mkLambda (n, t, c)) (f d))
    d

(* Zoom in, search, and wrap the result in a prod from binding (n : t) *)
let zoom_wrap_prod f n t (d : goal_proof_diff) : candidates =
  zoom_search
    (fun d -> List.map (fun c -> mkProd (n, t, c)) (f d))
    d

(* Zoom in, search, and unshift the result *)
let zoom_unshift f (d : goal_proof_diff) : candidates =
  zoom_search
    (fun d -> List.map unshift (f d))
    d

(* --- Zoomers on terms, instead of proof categories --- *)

(* Zoom into a term *)
let rec zoom_n_prod env npm typ : env * types =
  if npm = 0 then
    (env, typ)
  else
    match kind typ with
    | Prod (n1, t1, b1) ->
       zoom_n_prod (push_local (n1, t1) env) (npm - 1) b1
    | _ ->
       failwith "more parameters expected"

(* Lambda version *)
let zoom_n_lambda env npm trm : env * types =
  let (env, typ) = zoom_n_prod env npm (lambda_to_prod trm) in
  (env, prod_to_lambda typ)

(* Zoom all the way into a lambda term *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_local (n, t) env) b
  | _ ->
     (env, trm)

(* Zoom all the way into a product type *)
let rec zoom_product_type (env : env) (typ : types) : env * types =
  match kind typ with
  | Prod (n, t, b) ->
     zoom_product_type (push_local (n, t) env) b
  | _ ->
     (env, typ)

(* Zoom into the environment *)
let zoom_env zoom (env : env) (trm : types) : env =
  fst (zoom env trm)

(* Zoom into the term *)
let zoom_term zoom (env : env) (trm : types) : types =
  snd (zoom env trm)

(* --- Reconstruction after zooming into terms --- *)

(* Reconstruct a lambda from an environment, but stop when i are left *)
let rec reconstruct_lambda_n (env : env) (b : types) (i : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda_n env' (mkLambda (n, t, b)) i

(* Reconstruct a lambda from an environment *)
let reconstruct_lambda (env : env) (b : types) : types =
  reconstruct_lambda_n env b 0

(* Like reconstruct_lambda_n, but first skip j elements *)
let rec reconstruct_lambda_n_skip (env : env) (b : types) (i : int) (j : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    if j <= 0 then
      reconstruct_lambda_n_skip env' (mkLambda (n, t, b)) i j
    else
      reconstruct_lambda_n_skip env' (unshift b) (i - 1) (j - 1)
                

(* Reconstruct a product from an environment, but stop when i are left *)
let rec reconstruct_product_n (env : env) (b : types) (i : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_product_n env' (mkProd (n, t, b)) i

(* Reconstruct a product from an environment *)
let reconstruct_product (env : env) (b : types) : types =
  reconstruct_product_n env b 0

(* Like reconstruct_product_n, but first skip j elements *)
let rec reconstruct_product_n_skip (env : env) (b : types) (i : int) (j : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    if j <= 0 then
      reconstruct_product_n_skip env' (mkProd (n, t, b)) i j
    else
      reconstruct_product_n_skip env' (unshift b) (i - 1) (j - 1)
