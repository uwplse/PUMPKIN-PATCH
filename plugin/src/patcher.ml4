DECLARE PLUGIN "patch"

open Term
open Names
open Environ
open Coqterms
open Assumptions
open Evaluation
open Proofdiff
open Search
open Constrexpr
open Substitution
open Printing
open Inverting
open Theorem
open Lifting
open Debruijn
open Searchopts
open Specialization
open Factoring

(*
 * Plugin for patching Coq proofs given a change.
 *
 * This is the top-level. It exposes commands to users,
 * which call different procedures under the hood depending
 * on what has changed.  The procedures compose the core components
 * in different ways.
 *
 * This file also exposes some of the core components as
 * commands themselves.
 *)

(* --- Auxiliary functionality for top-level functions --- *)

(* Intern terms corresponding to two definitions *)
let intern_defs d1 d2 : types * types =
  let (evm, env) = Lemmas.get_current_context() in
  let d1 = intern env evm d1 in
  let d2 = intern env evm d2 in
  (unwrap_definition env d1, unwrap_definition env d2)

(* Initialize diff & search configuration *)
let configure trm1 trm2 cut : goal_proof_diff * options =
  let (evm, env) = Lemmas.get_current_context() in
  let cut_term = Option.map (intern env evm) cut in
  let lemma = Option.map (build_cut_lemma env) cut_term in
  let c1 = eval_proof env trm1 in
  let c2 = eval_proof env trm2 in
  let d = add_goals (difference c1 c2 no_assumptions) in
  (d, configure_search d lemma)

(* Common inversion functionality *)
let invert_patch n env evm patch =
  let inverted = invert_terms invert_factor env [patch] in
  try
    let patch_inv = List.hd inverted in
    let _ = infer_type env patch_inv in
    define_term n env evm patch_inv;
    Printf.printf "Defined %s\n" (Id.to_string n)
  with _ ->
    failwith "Could not find a well-typed inverted term"

(* Common patch command functionality *)
let patch n old_term new_term try_invert a search =
  let (evm, env) = Lemmas.get_current_context() in
  let reduce = reduce_using (try_reduce reduce_remove_identities) in
  let patch = reduce env (search env evm a) in
  let prefix = Id.to_string n in
  define_term n env evm patch;
  Printf.printf "Defined %s\n" prefix;
  if try_invert then
    try
      let inv_n_string = String.concat "_" [prefix; "inv"] in
      let inv_n = Id.of_string inv_n_string in
      invert_patch inv_n env evm patch
    with _ ->
      ()
  else
    ()

(* --- Commands --- *)

(*
 * Command functionality for generating reusable patches
 * Patch Proof, Patch Definition, and Patch Constructor all call this
 * The latter two just pass extra guidance for now
 *)
let patch_proof n d_old d_new cut =
  let (old_term, new_term) = intern_defs d_old d_new in
  let (d, opts) = configure old_term new_term cut in
  let kind_of_change = get_change opts in
  let try_invert = not (is_conclusion kind_of_change) in
  patch n old_term new_term try_invert ()
    (fun env evm _ ->
      search_for_patch old_term opts d)

(*
 * The Patch Theorem command functionality
 * This is an experimental dependent substitution command
 * It doesn't do search, so it's really not a patch finding procedure
 * It's also not a component
 * It just might be useful in the future, so feel free to play with it
 *)
let patch_theorem n d_old d_new t =
  let (evm, env) = Lemmas.get_current_context() in
  let (old_term, new_term) = (intern env evm d_old, intern env evm d_new) in
  patch n old_term new_term false t
    (fun env evm t ->
      let theorem = intern env evm t in
      let t_trm = lookup_definition env theorem in
      update_theorem env old_term new_term t_trm)

(* Invert a term *)
let invert n trm : unit =
  let (evm, env) = Lemmas.get_current_context() in
  let body = lookup_definition env (intern env evm trm) in
  invert_patch n env evm body

(* Specialize a term *)
let specialize n trm : unit =
  let (evm, env) = Lemmas.get_current_context() in
  let reducer = specialize_body specialize_term in
  let specialized = reduce_using reducer env (intern env evm trm) in
  define_term n env evm specialized

(* Abstract a term by a function *)
let abstract n trm goal : unit =
  let (evm, env) = Lemmas.get_current_context() in
  let c = lookup_definition env (intern env evm trm) in
  let goal_type = intern env evm goal in
  let strategies = reduce_strategies_prop goal_type in
  let (_, _, goal_b) = destProd goal_type in
  let rec abstract_term env c g =
    match (kind_of_term c, kind_of_term g) with
    | (Lambda (n, t, cb), Prod (_, tb, gb)) when isLambda cb && isProd gb ->
       abstract_term (push_rel (n, None, t) env) cb gb
    | (Lambda (_, _, _), Prod (_, gt, _)) when isApp gt ->
       let ct = infer_type env c in
       let (_, _, ctb) = destProd ct in
       if isApp ctb then
         let (f_base, _) = destApp (unshift ctb) in
         let f_goal = f_base in
         let args = Array.to_list (snd (destApp gt)) in
         let cs = [c] in
         let is_concrete = true in
         let abstraction_config = {is_concrete; env; args; cs; f_base; f_goal; strategies} in
         let lcs = abstract_with_strategies abstraction_config in
         if List.length lcs > 0 then
           define_term n env evm (List.hd lcs)
         else
           failwith "Failed to generalize"
       else
         failwith "Cannot infer property to generalize"
    | _ ->
       failwith "Goal is inconsistent with term to generalize"
  in abstract_term env c goal_b

(* Factor a term into a sequence of lemmas *)
let factor n trm : unit =
  let (evm, env) = Lemmas.get_current_context() in
  let body = lookup_definition env (intern env evm trm) in
  let fs = reconstruct_factors (factor_term env body) in
  let prefix = Id.to_string n in
  try
    List.iteri
      (fun i lemma ->
        let lemma_id_string = String.concat "_" [prefix; string_of_int i] in
        let lemma_id = Id.of_string lemma_id_string in
        define_term lemma_id env evm lemma;
        Printf.printf "Defined %s\n" lemma_id_string)
      fs
  with _ -> failwith "Could not find lemmas"

(* Patch command *)
VERNAC COMMAND EXTEND PatchProof CLASSIFIED AS SIDEFF
| [ "Patch" "Proof" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ patch_proof n d_old d_new None ]
| [ "Patch" "Proof" constr(d_old) constr(d_new) "cut" "by" constr(cut) "as" ident(n)] ->
  [ patch_proof n d_old d_new (Some cut) ]
| [ "Patch" "Theorem" constr(d_old) constr(d_new) constr(t) "as" ident(n)] ->
  [ patch_theorem n d_old d_new t ]
END

(* Invert a term *)
VERNAC COMMAND EXTEND InvertCandidate CLASSIFIED AS SIDEFF
| [ "Invert" constr(trm) "as" ident(n)] ->
  [ invert n trm ]
END

(* Specialize a patch *)
VERNAC COMMAND EXTEND SpecializeCandidate CLASSIFIED AS SIDEFF
| [ "Specialize" constr(trm) "as" ident(n)] ->
  [ specialize n trm ]
END

(*
 * Abstract a term by a function
 *
 * We don't yet expose top-level functionality for abstracting
 * by arguments, though it's used internally by patch finding
 * procedures
 *)
VERNAC COMMAND EXTEND AbstractCandidate CLASSIFIED AS SIDEFF
| [ "Abstract" constr(trm) "to" constr(goal) "as" ident(n)] ->
  [ abstract n trm goal ]
END

(* Factor a term into a sequence of lemmas *)
VERNAC COMMAND EXTEND FactorCandidate CLASSIFIED AS SIDEFF
| [ "Factor" constr(trm) "using" "prefix" ident(n) ] ->
  [ factor n trm ]
END
