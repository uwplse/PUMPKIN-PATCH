
DECLARE PLUGIN "patch"

open Constr
open Names
open Environ
open Assumptions
open Evaluation
open Proofdiff
open Search
open Evd
open Printing
open Inverting
open Theorem
open Abstraction
open Abstractionconfig
open Searchopts
open Reducers
open Specialization
open Factoring
open Cutlemma
open Kindofchange
open Changedetectors
open Stdarg
open Utilities
open Zooming
open Defutils
open Envutils

module Globmap = Globnames.Refmap

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

(* --- Options --- *)

(*
 * Print the definitions of patches PUMPKIN finds
 *)
let opt_printpatches = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Print patches PUMPKIN finds";
  Goptions.optkey = ["PUMPKIN"; "Printing"];
  Goptions.optread = (fun () -> !opt_printpatches);
  Goptions.optwrite = (fun b -> opt_printpatches := b);
}

(* --- Auxiliary functionality for top-level functions --- *)

(* Intern terms corresponding to two definitions *)
let intern_defs d1 d2 : evar_map * types * types =
  let (evm, env) = Pfedit.get_current_context() in
  let evm, d1 = intern env evm d1 in
  let evm, d2 = intern env evm d2 in
  (evm, unwrap_definition env d1, unwrap_definition env d2)

(* Initialize diff & search configuration *)
let configure trm1 trm2 cut : goal_proof_diff * options =
  let (evm, env) = Pfedit.get_current_context() in
  let cut_term = Option.map (intern env evm) cut in
  let lemma = Option.map (fun evm, t -> build_cut_lemma env t) cut_term in
  let c1 = eval_proof env trm1 in
  let c2 = eval_proof env trm2 in
  let d = add_goals (difference c1 c2 no_assumptions) in
  let change = find_kind_of_change evm lemma d in
  (d, configure_search d change lemma)

(* Initialize diff & search configuration for optimization *)
let configure_optimize trm : goal_proof_diff * options =
  let (evm, env) = Pfedit.get_current_context () in
  let c = eval_proof env trm in
  let d = add_goals (difference c c no_assumptions) in
  let change = Identity in
  (d, configure_search d change None)

(* Common inversion functionality *)
let invert_patch n env evm patch =
  let inverted = invert_terms invert_factor env evm [patch] in
  try
    let patch_inv = List.hd inverted in
    let _ = infer_type env evm patch_inv in
    ignore (define_term n evm patch_inv false);
    let n_string = Id.to_string n in
    if !opt_printpatches then
      print_patch env evm n_string patch_inv
    else
      Printf.printf "Defined %s\n" (Id.to_string n)
  with _ ->
    failwith "Could not find a well-typed inverted term"

(* Common patch command functionality *)
let patch env evm n try_invert a search =
  let reduce = try_reduce reduce_remove_identities in
  let patch_to_red = search env evm a in
  let patch = reduce env evm patch_to_red in
  let prefix = Id.to_string n in
  ignore (define_term n evm patch false);
  (if !opt_printpatches then
    print_patch env evm prefix patch
  else
    Printf.printf "Defined %s\n" prefix);
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
  let (evm, env) = Pfedit.get_current_context () in
  let (evm, old_term, new_term) = intern_defs d_old d_new in
  let (d, opts) = configure old_term new_term cut in
  let change = get_change opts in
  let try_invert = not (is_conclusion change || is_hypothesis change) in
  patch env evm n try_invert ()
    (fun env evm _ ->
      search_for_patch evm old_term opts d)

(*
 * Command functionality for optimizing proofs.
 *
 * This builds on Patch Proof to do basic proof optimization
 * by removing unused induction principles. Basically,
 * this performs proof patching against "nothing" with the same structure.
 * Since we can't actually represet "nothing," and using other identities
 * (like unit) means messing with heuristics, we instead represent
 * this as a special configuration, and pass in the same term twice.
 *)
let optimize_proof n d =
  let (evm, env) = Pfedit.get_current_context () in
  let evm, def = intern env evm d in
  let trm = unwrap_definition env def in
  let (d, opts) = configure_optimize trm in
  patch env evm n false ()
    (fun env evm _ ->
      search_for_patch evm trm opts d)

(*
 * The Patch Theorem command functionality
 * This is an experimental dependent substitution command
 * It doesn't do search, so it's really not a patch finding procedure
 * It's also not a component
 * It just might be useful in the future, so feel free to play with it
 *)
let patch_theorem n d_old d_new t =
  let (evm, env) = Pfedit.get_current_context() in
  let evm, old_term = intern env evm d_old in
  let evm, new_term = intern env evm d_new in
  patch env evm n false t
    (fun env evm t ->
      let evm, theorem = intern env evm t in
      let t_trm = lookup_definition env theorem in
      update_theorem env evm old_term new_term t_trm)

(* Invert a term *)
let invert n trm : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let evm, def = intern env evm trm in
  let body = lookup_definition env def in
  invert_patch n env evm body

(* Specialize a term *)
let specialize n trm : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let reducer = specialize_body specialize_term in
  let evm, def = intern env evm trm in
  let specialized = reducer env evm def in
  ignore (define_term n evm specialized false)

(* Abstract a term by a function or arguments *)
let abstract n trm goal : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let evm, def = intern env evm trm in
  let c = lookup_definition env def in
  let evm, goal_def = intern env evm goal in
  let goal_type = unwrap_definition env goal_def in
  let config = configure_from_goal env evm goal_type c in
  let abstracted = abstract_with_strategies config in
  if List.length abstracted > 0 then
    try
      ignore (define_term n evm (List.hd abstracted) false)
    with _ -> (* Temporary, hack to support arguments *)
      let num_args = List.length (config.args_base) in
      let num_discard = nb_rel config.env - num_args in
      let rels = List.map (fun i -> i + num_discard) (from_one_to num_args) in
      let args = Array.map (fun i -> mkRel i) (Array.of_list rels) in
      let app = mkApp (List.hd abstracted, args) in
      let reduced = reduce_term config.env evm app in
      let reconstructed = reconstruct_lambda config.env reduced in
      ignore (define_term n evm reconstructed false)
  else
    failwith "Failed to abstract"

(* Factor a term into a sequence of lemmas *)
let factor n trm : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let evm, def = intern env evm trm in
  let body = lookup_definition env def in
  let fs = reconstruct_factors (factor_term env evm body) in
  let prefix = Id.to_string n in
  try
    List.iteri
      (fun i lemma ->
        let lemma_id_string = String.concat "_" [prefix; string_of_int i] in
        let lemma_id = Id.of_string lemma_id_string in
        ignore (define_term lemma_id evm lemma false);
        Printf.printf "Defined %s\n" lemma_id_string)
      fs
  with _ -> failwith "Could not find lemmas"

(* --- Vernac syntax --- *)

(* Patch command *)
VERNAC COMMAND EXTEND PatchProof CLASSIFIED AS SIDEFF
| [ "Patch" "Proof" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ patch_proof n d_old d_new None ]
| [ "Patch" "Proof" constr(d_old) constr(d_new) "cut" "by" constr(cut) "as" ident(n)] ->
  [ patch_proof n d_old d_new (Some cut) ]
| [ "Patch" "Theorem" constr(d_old) constr(d_new) constr(t) "as" ident(n)] ->
  [ patch_theorem n d_old d_new t ]
END

(* Optimize command *)
VERNAC COMMAND EXTEND OptimizeProofTerm CLASSIFIED AS SIDEFF
| [ "Optimize" "Proof" "Term" constr(d) "as" ident(n)] ->
  [ optimize_proof n d ]
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

(* Abstract a term by a function or by its arguments *)
VERNAC COMMAND EXTEND AbstractCandidate CLASSIFIED AS SIDEFF
| [ "Abstract" constr(trm) "to" constr(goal) "as" ident(n)] ->
  [ abstract n trm goal ]
END

(* Factor a term into a sequence of lemmas *)
VERNAC COMMAND EXTEND FactorCandidate CLASSIFIED AS SIDEFF
| [ "Factor" constr(trm) "using" "prefix" ident(n) ] ->
  [ factor n trm ]
END
