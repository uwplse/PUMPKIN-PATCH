
DECLARE PLUGIN "patch"

open Constr
open Names
open Environ
open Assumptions
open Evaluation
open Proofdiff
open Search
open Evd
open Proofcat
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
open Stateutils
open Inference
open Proofcatterms

module Globmap = Globnames.Refmap

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
let intern_defs env d1 d2 =
  bind
    (map_tuple_state (fun t sigma -> intern env sigma t) (d1, d2))
    (fun (d1, d2) ->
      ret (unwrap_definition env d1, unwrap_definition env d2))

(* Initialize diff & search configuration *)
let configure env trms cut sigma =
  let cut_term = Option.map (intern env sigma) cut in
  let lemma = Option.map (fun (_, t) -> build_cut_lemma env t) cut_term in
  bind
    (map_tuple_state (fun trm sigma -> infer_type env sigma trm) trms)
    (fun goals ->
      bind
        (find_kind_of_change lemma env trms goals)
        (fun change ->
	  ret (goals, configure_search env change lemma)))
    sigma

(* Initialize diff & search configuration for optimization *)
let configure_optimize env trm =
  bind
    (fun sigma -> infer_type env sigma trm)
    (fun goal ->
      let goals = (goal, goal) in
      ret (goals, configure_search env Identity None))

(* Common inversion functionality *)
let invert_patch n env patch sigma =
  let sigma, inverted = invert_terms invert_factor env [patch] sigma in
  try
    let patch_inv = List.hd inverted in
    let sigma, _ = infer_type env sigma patch_inv in
    ignore (define_term n sigma patch_inv false);
    let n_string = Id.to_string n in
    if !opt_printpatches then
      print_patch env sigma n_string patch_inv
    else
      Printf.printf "Defined %s\n" (Id.to_string n)
  with _ ->
    failwith "Could not find a well-typed inverted term"

(* Common patch command functionality *)
let patch env n try_invert a search sigma =
  let reduce = try_reduce reduce_remove_identities in
  let sigma, patch_to_red = search env a sigma in
  let sigma, patch = reduce env sigma patch_to_red in
  let prefix = Id.to_string n in
  ignore (define_term n sigma patch false);
  (if !opt_printpatches then
    print_patch env sigma prefix patch
  else
    Printf.printf "Defined %s\n" prefix);
  if try_invert then
    try
      let inv_n_string = String.concat "_" [prefix; "inv"] in
      let inv_n = Id.of_string inv_n_string in
      invert_patch inv_n env patch sigma
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
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, trms = intern_defs env d_old d_new sigma in
  let sigma, (goals, opts) = configure env trms cut sigma in
  let change = get_change opts in
  let try_invert = not (is_conclusion change || is_hypothesis change) in
  let search _ _ = search_for_patch opts env trms goals in
  patch env n try_invert () search sigma

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
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, def = intern env sigma d in
  let trm = unwrap_definition env def in
  let sigma, (goals, opts) = configure_optimize env trm sigma in
  let search _ _ = search_for_patch opts env (trm, trm) goals in
  patch env n false () search sigma

(*
 * The Patch Theorem command functionality
 * This is an experimental dependent substitution command
 * It doesn't do search, so it's really not a patch finding procedure
 * It's also not a component
 * It just might be useful in the future, so feel free to play with it
 *)
let patch_theorem n d_old d_new t =
  let (sigma, env) = Pfedit.get_current_context() in
  let sigma, old_term = intern env sigma d_old in
  let sigma, new_term = intern env sigma d_new in
  let search env t sigma =
    let sigma, theorem = intern env sigma t in
    let t_trm = lookup_definition env theorem in
    update_theorem env old_term new_term t_trm sigma
  in patch env n false t search sigma

(* Invert a term *)
let invert n trm : unit =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, def = intern env sigma trm in
  let body = lookup_definition env def in
  invert_patch n env body sigma

(* Specialize a term *)
let specialize n trm : unit =
  let (sigma, env) = Pfedit.get_current_context () in
  let reducer = specialize_body specialize_term in
  let sigma, def = intern env sigma trm in
  let sigma, specialized = reducer env sigma def in
  ignore (define_term n sigma specialized false)

(* Abstract a term by a function or arguments *)
let abstract n trm goal : unit =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, def = intern env sigma trm in
  let c = lookup_definition env def in
  let sigma, goal_def = intern env sigma goal in
  let goal_type = unwrap_definition env goal_def in
  let sigma, config = configure_from_goal env goal_type c sigma in
  let sigma, abstracted = abstract_with_strategies config sigma in
  if List.length abstracted > 0 then
    try
      ignore (define_term n sigma (List.hd abstracted) false)
    with _ -> (* Temporary, hack to support arguments *)
      let num_args = List.length (config.args_base) in
      let num_discard = nb_rel config.env - num_args in
      let rels = List.map (fun i -> i + num_discard) (from_one_to num_args) in
      let args = Array.map (fun i -> mkRel i) (Array.of_list rels) in
      let app = mkApp (List.hd abstracted, args) in
      let sigma, reduced = reduce_term config.env sigma app in
      let reconstructed = reconstruct_lambda config.env reduced in
      ignore (define_term n sigma reconstructed false)
  else
    failwith "Failed to abstract"

(* Factor a term into a sequence of lemmas *)
let factor n trm : unit =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, def = intern env sigma trm in
  let body = lookup_definition env def in
  let sigma, fs =
    bind
      (factor_term env body)
      (fun fs -> ret (reconstruct_factors fs))
      sigma
  in
  let prefix = Id.to_string n in
  try
    List.iteri
      (fun i lemma ->
        let lemma_id_string = String.concat "_" [prefix; string_of_int i] in
        let lemma_id = Id.of_string lemma_id_string in
        ignore (define_term lemma_id sigma lemma false);
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
