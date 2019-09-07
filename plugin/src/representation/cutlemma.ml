(* --- Cutting by intermediate lemmas/guiding search --- *)

open Constr
open Environ
open Evd
open Reducers
open Debruijn
open Utilities
open Typehofs
open Contextutils
open Envutils
open Convertibility
open Stateutils
open Inference

(* --- TODO temporary for refactor: should use this order in lib at some point --- *)

let on_red_type_default f env trm sigma =
  Typehofs.on_red_type_default
    (fun env sigma trm -> f env trm sigma)
    env
    sigma
    trm

let reduce_term env trm sigma =
  reduce_term env sigma trm

let infer_type env trm sigma =
  infer_type env sigma trm
       
(* --- End TODO --- *)
       
type cut_lemma =
  {
    lemma : types;
    app : types;
  }

let build_cut_lemma (env : env) (app : types) : cut_lemma =
  let (_, t, _) = destLambda app in
  let lemma = lookup_definition env t in
  { lemma; app; }

let get_lemma (cut : cut_lemma) =
  cut.lemma

let get_app (cut : cut_lemma) =
  cut.app

(* Test if a type is exactly the type of the lemma to cut by *)
let is_cut_strict env lemma typ sigma =
  try
    let sigma, lemma = reduce_term env lemma sigma in
    let sigma, typ = reduce_term env typ sigma in
    concls_convertible env sigma lemma typ
  with _ ->
    sigma, false

(* Test if a term has exactly the type of the lemma to cut by *)
let has_cut_type_strict env cut trm =
  try (* TODO do we need red type here or not? same everywhere *)
    on_red_type_default
      (fun env -> is_cut_strict env (get_lemma cut))
      env
      trm 
  with _ ->
    ret false

(* Flip the conclusions of a cut lemma *)
let rec flip_concls lemma =
  match kind lemma with
  | Prod (n, t, b) when isProd b ->
     mkProd (n, t, flip_concls b)
  | Prod (n, t, b) ->
     mkProd (n, unshift b, shift t)
  | _ ->
     failwith "Could not reverse the lemma conclusions"

(*
 * Test if a term has exactly the type of the lemma to cut by in reverse
 *
 * POST-DEADLINE: Having both of these is messy/creates extra candidates.
 * Determine which one to use based on search goals, direction, options,
 * and candidates.
 *)
let has_cut_type_strict_rev env cut trm =
  try
    on_red_type_default
      (fun env -> is_cut_strict env (flip_concls (get_lemma cut)))
      env
      trm
  with _ ->
    ret false

(* Test if a term has the type of the lemma or its reverse *)
let has_cut_type_strict_sym env cut trm =
  branch_state
    (has_cut_type_strict env cut)
    (fun _ -> ret true)
    (has_cut_type_strict_rev env cut)
    trm

(* Check if a type is loosely the cut lemma (can have extra hypotheses) *)
let rec is_cut env lemma typ =
  match map_tuple kind (lemma, typ) with
  | (Prod (nl, tl, bl), Prod (nt, tt, bt)) ->
     if not (isProd bl || isProd bt) then
       is_cut_strict env lemma typ
     else
       branch_state
         (fun tt sigma -> convertible env sigma tl tt)
         (fun _ -> is_cut (push_local (nl, tl) env) bl bt)
         (fun _ ->
           branch_state
             (fun bl -> is_cut (push_local (nl, tl) env) bl (shift typ))
             (fun _ -> ret true)
             (fun _ -> is_cut (push_local (nt, tt) env) (shift lemma) bt)
             bl)
         tt
  | _  ->
     ret false

(* Check if a term has loosely the cut lemma type (can have extra hypotheses) *)
let has_cut_type env cut trm =
  try
    on_red_type_default (fun env -> is_cut env (get_lemma cut)) env trm
  with _ ->
    ret false

(* Check if a term is loosely an application of the lemma to cut by *)
let has_cut_type_app env cut trm =
  try
    let env_cut = push_local (Names.Name.Anonymous, get_lemma cut) env in
    bind
      (on_red_type_default (fun _ trm -> ret (shift trm)) env trm)
      (fun typ ->
        bind
          (reduce_term env_cut (mkApp (get_app cut, Array.make 1 (mkRel 1))))
          (fun app_app ->
            bind
              (infer_type env_cut app_app)
              (fun app_app_typ -> is_cut env_cut app_app_typ typ)))
  with _ ->
    ret false

(* Check if a term is consistent with the cut type *)
let consistent_with_cut env cut trm =
  let rec consistent en c t =
    match map_tuple kind (c, t) with
    | (Prod (n, t, cb), Lambda (_, _, b)) when isProd cb && isLambda b ->
       consistent (push_rel CRD.(LocalAssum(n, t)) en) cb b
    | (Prod (_, ct, cb), Lambda (_, _, _)) ->
       true
    | _ ->
       false
  in consistent env (get_lemma cut) trm

(* Filter a list of terms to those with the (loose) cut lemma type *)
let filter_cut env cut trms =
  filter_state (has_cut_type env cut) trms

(* Filter a list of terms to those that apply the (loose) cut lemma type *)
let filter_applies_cut env cut trms =
  filter_state (has_cut_type_app env cut) trms

(*
 * Filter a list of terms to those that are consistent with the cut type
 * Enter the term lambdas so that they are offset by the same amount
 *)
let filter_consistent_cut env cut trms =
  let rec make_consistent en c t =
    match map_tuple kind (c, t) with
    | (Prod (n, t, cb), Lambda (_, _, b)) when isProd cb && isLambda b ->
       make_consistent (push_rel CRD.(LocalAssum(n, t)) en) cb b
    | _ ->
       t
  in
  List.map
    (make_consistent env (get_lemma cut))
    (List.filter (consistent_with_cut env cut) trms)

(* This returns true when the candidates we have patch the lemma we cut by *)
let are_cut env cut cs =
  bind
    (filter_cut env cut cs)
    (fun trms -> ret (List.length trms = List.length cs))
