(* --- Cutting by intermediate lemmas/guiding search --- *)

open Constr
open Environ
open Reducers
open Coqterms
open Debruijn
open Collections

module CRD = Context.Rel.Declaration

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
let is_cut_strict env evd lemma typ =
  try
    concls_convertible env (reduce_term env evd lemma) (reduce_term env evd typ)
  with _ ->
    false

(* Test if a term has exactly the type of the lemma to cut by *)
let has_cut_type_strict env evd cut trm =
  try
    let typ = reduce_term env evd (infer_type env trm) in
    is_cut_strict env evd (get_lemma cut) typ
  with _ ->
    false

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
    let typ = reduce_term env evd (infer_type env trm) in
    is_cut_strict env evd (flip_concls (get_lemma cut)) typ
  with _ ->
    false

(* Test if a term has the type of the lemma or its reverse *)
let has_cut_type_strict_sym env evd cut trm =
  has_cut_type_strict env evd cut trm || has_cut_type_strict_rev env evd cut trm

(* Check if a type is loosely the cut lemma (can have extra hypotheses) *)
let rec is_cut env evd lemma typ =
  match kinds_of_terms (lemma, typ) with
  | (Prod (nl, tl, bl), Prod (nt, tt, bt)) ->
     if not (isProd bl || isProd bt) then
       is_cut_strict env evd lemma typ
     else
       if convertible env tl tt then
         is_cut (push_rel CRD.(LocalAssum(nl, tl)) env) evd bl bt
       else
         let cut_l = is_cut (push_rel CRD.(LocalAssum(nl, tl)) env) evd bl (shift typ) in
         let cut_r = is_cut (push_rel CRD.(LocalAssum(nt, tt)) env) evd (shift lemma) bt in
         cut_l || cut_r
  | _  ->
     false

(* Check if a term has loosely the cut lemma type (can have extra hypotheses) *)
let has_cut_type env evd cut trm =
  try
    let typ = reduce_term env evd (infer_type env trm) in
    is_cut env evd (get_lemma cut) typ
  with _ ->
    false

(* Check if a term is loosely an application of the lemma to cut by *)
let has_cut_type_app env evd cut trm =
  try
    let typ = shift (reduce_term env evd (infer_type env trm)) in
    let env_cut = push_rel CRD.(LocalAssum(Names.Name.Anonymous, get_lemma cut)) env in
    let app = get_app cut in
    let app_app = reduce_term env_cut evd (mkApp (app, singleton_array (mkRel 1))) in
    let app_app_typ = infer_type env_cut app_app in
    is_cut env_cut evd app_app_typ typ
  with _ ->
    false

(* Check if a term is consistent with the cut type *)
let consistent_with_cut env cut trm =
  let rec consistent en c t =
    match kinds_of_terms (c, t) with
    | (Prod (n, t, cb), Lambda (_, _, b)) when isProd cb && isLambda b ->
       consistent (push_rel CRD.(LocalAssum(n, t)) en) cb b
    | (Prod (_, ct, cb), Lambda (_, _, _)) ->
       true
    | _ ->
       false
  in consistent env (get_lemma cut) trm

(* Filter a list of terms to those with the (loose) cut lemma type *)
let filter_cut env evd cut trms =
  List.filter (has_cut_type env evd cut) trms

(* Filter a list of terms to those that apply the (loose) cut lemma type *)
let filter_applies_cut env evd cut trms =
  List.filter (has_cut_type_app env evd cut) trms

(*
 * Filter a list of terms to those that are consistent with the cut type
 * Enter the term lambdas so that they are offset by the same amount
 *)
let filter_consistent_cut env cut trms =
  let rec make_consistent en c t =
    match kinds_of_terms (c, t) with
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
  List.length (filter_cut env evd cut cs) = List.length cs
