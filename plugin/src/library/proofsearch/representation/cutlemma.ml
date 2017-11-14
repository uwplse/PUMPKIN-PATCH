(* --- Cutting by intermediate lemmas/guiding search --- *)

open Term
open Environ
open Reducers
open Coqterms
open Debruijn
open Collections

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
let is_cut_strict env lemma typ =
  try
    concls_convertible env (reduce_term env lemma) (reduce_term env typ)
  with _ ->
    false

(* Test if a term has exactly the type of the lemma to cut by *)
let has_cut_type_strict env cut trm =
  try
    let typ = reduce_term env (infer_type env trm) in
    is_cut_strict env (get_lemma cut) typ
  with _ ->
    false

(* Flip the conclusions of a cut lemma *)
let rec flip_concls lemma =
  match kind_of_term lemma with
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
    let typ = reduce_term env (infer_type env trm) in
    is_cut_strict env (flip_concls (get_lemma cut)) typ
  with _ ->
    false

(* Test if a term has the type of the lemma or its reverse *)
let has_cut_type_strict_sym env cut trm =
  has_cut_type_strict env cut trm || has_cut_type_strict_rev env cut trm

(* Check if a type is loosely the cut lemma (can have extra hypotheses) *)
let rec is_cut env lemma typ =
  match kinds_of_terms (lemma, typ) with
  | (Prod (nl, tl, bl), Prod (nt, tt, bt)) ->
     if not (isProd bl || isProd bt) then
       is_cut_strict env lemma typ
     else
       if convertible env tl tt then
         is_cut (push_rel (nl, None, tl) env) bl bt
       else
         let cut_l = is_cut (push_rel (nl, None, tl) env) bl (shift typ) in
         let cut_r = is_cut (push_rel (nt, None, tt) env) (shift lemma) bt in
         cut_l || cut_r
  | _  ->
     false

(* Check if a term has loosely the cut lemma type (can have extra hypotheses) *)
let has_cut_type env cut trm =
  try
    let typ = reduce_term env (infer_type env trm) in
    is_cut env (get_lemma cut) typ
  with _ ->
    false

(* Check if a term is loosely an application of the lemma to cut by *)
let has_cut_type_app env cut trm =
  try
    let typ = shift (reduce_term env (infer_type env trm)) in
    let env_cut = push_rel (Anonymous, None, get_lemma cut) env in
    let app = get_app cut in
    let app_app = reduce_term env_cut (mkApp (app, singleton_array (mkRel 1))) in
    let app_app_typ = infer_type env_cut app_app in
    is_cut env_cut app_app_typ typ
  with _ ->
    false

(* Check if a term is consistent with the cut type *)
let consistent_with_cut env cut trm =
  let rec consistent en c t =
    match kinds_of_terms (c, t) with
    | (Prod (n, t, cb), Lambda (_, _, b)) when isProd cb && isLambda b ->
       consistent (push_rel (n, None, t) en) cb b
    | (Prod (_, ct, cb), Lambda (_, _, _)) ->
       true
    | _ ->
       false
  in consistent env (get_lemma cut) trm

(* Filter a list of terms to those with the (loose) cut lemma type *)
let filter_cut env cut trms =
  List.filter (has_cut_type env cut) trms

(* Filter a list of terms to those that apply the (loose) cut lemma type *)
let filter_applies_cut env cut trms =
  List.filter (has_cut_type_app env cut) trms

(*
 * Filter a list of terms to those that are consistent with the cut type
 * Enter the term lambdas so that they are offset by the same amount
 *)
let filter_consistent_cut env cut trms =
  let rec make_consistent en c t =
    match kinds_of_terms (c, t) with
    | (Prod (n, t, cb), Lambda (_, _, b)) when isProd cb && isLambda b ->
       make_consistent (push_rel (n, None, t) en) cb b
    | _ ->
       t
  in
  List.map
    (make_consistent env (get_lemma cut))
    (List.filter (consistent_with_cut env cut) trms)

(* This returns true when the candidates we have patch the lemma we cut by *)
let are_cut env cut cs =
  List.length (filter_cut env cut cs) = List.length cs