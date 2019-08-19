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
let is_cut_strict env sigma lemma typ =
  try
    let sigma, lemma = reduce_term env sigma lemma in
    let sigma, typ = reduce_term env sigma typ in
    concls_convertible env sigma lemma typ
  with _ ->
    sigma, false

(* Test if a term has exactly the type of the lemma to cut by *)
let has_cut_type_strict env sigma cut trm =
  try (* TODO do we need red type here or not? same everywhere *)
    on_red_type_default (fun env sigma -> is_cut_strict env sigma (get_lemma cut)) env sigma trm 
  with _ ->
    sigma, false

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
let has_cut_type_strict_rev env evd cut trm =
  try
    on_red_type_default (fun env evd -> is_cut_strict env evd (flip_concls (get_lemma cut))) env evd trm
  with _ ->
    evd, false

(* Test if a term has the type of the lemma or its reverse *)
let has_cut_type_strict_sym env evd cut trm =
  branch_state
    (fun trm sigma -> has_cut_type_strict env sigma cut trm)
    (fun _ -> ret true)
    (fun trm sigma -> has_cut_type_strict_rev env sigma cut trm)
    trm
    evd

(* Check if a type is loosely the cut lemma (can have extra hypotheses) *)
let rec is_cut env sigma lemma typ =
  match map_tuple kind (lemma, typ) with
  | (Prod (nl, tl, bl), Prod (nt, tt, bt)) ->
     if not (isProd bl || isProd bt) then
       is_cut_strict env sigma lemma typ
     else
       branch_state
         (fun tt sigma -> convertible env sigma tl tt)
         (fun _ sigma -> is_cut (push_rel CRD.(LocalAssum(nl, tl)) env) sigma bl bt)
         (fun _ ->
           branch_state
             (fun bl sigma -> is_cut (push_rel CRD.(LocalAssum(nl, tl)) env) sigma bl (shift typ))
             (fun _ -> ret true)
             (fun _ sigma -> is_cut (push_rel CRD.(LocalAssum(nt, tt)) env) sigma (shift lemma) bt)
             bl)
         tt
         sigma
  | _  ->
     sigma, false

(* Check if a term has loosely the cut lemma type (can have extra hypotheses) *)
let has_cut_type env evd cut trm =
  try
    on_red_type_default (fun env evd -> is_cut env evd (get_lemma cut)) env evd trm
  with _ ->
    evd, false

(* Check if a term is loosely an application of the lemma to cut by *)
let has_cut_type_app env evd cut trm =
  try
    let evd, typ = on_red_type_default (fun env evd trm -> evd, shift trm) env evd trm in
    let env_cut = push_rel CRD.(LocalAssum(Names.Name.Anonymous, get_lemma cut)) env in
    let app = get_app cut in
    let evd, app_app = reduce_term env_cut Evd.empty (mkApp (app, Array.make 1 (mkRel 1))) in
    let app_app_typ = infer_type env_cut evd app_app in
    is_cut env_cut evd app_app_typ typ
  with _ ->
    evd, false

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
let filter_cut env evd cut trms =
  filter_state (fun trm evd -> has_cut_type env evd cut trm) trms evd

(* Filter a list of terms to those that apply the (loose) cut lemma type *)
let filter_applies_cut env evd cut trms =
  filter_state (fun trm evd -> has_cut_type_app env evd cut trm) trms evd

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
let are_cut env evd cut cs =
  bind
    (fun evd -> filter_cut env evd cut cs)
    (fun trms -> ret (List.length trms = List.length cs))
    evd
