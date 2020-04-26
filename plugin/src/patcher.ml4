
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
open Stateutils
open Inference
open Tactics
open Pp
open Ltac_plugin
open Nameutils
open Refactor
open Decompiler
   
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
let configure env trm1 trm2 cut sigma =
  let cut_term = Option.map (intern env sigma) cut in
  let lemma = Option.map (fun (_, t) -> build_cut_lemma env t) cut_term in
  bind
    (map_tuple_state (eval_proof env) (trm1, trm2))
    (fun (c1, c2) ->
      let d = add_goals (difference c1 c2 no_assumptions) in
      bind
        (find_kind_of_change lemma d)
        (fun change -> ret (d, configure_search d change lemma)))
    sigma

(* Initialize diff & search configuration for optimization *)
let configure_optimize env trm =
  bind
    (eval_proof env trm)
    (fun c ->
      let d = add_goals (difference c c no_assumptions) in
      ret (d, configure_search d Identity None))

(* Print message declaring that a patch, if any, was defined. *)
let debug_print_patch env sigma n patch =
  match n with
  | Some n ->
     if !opt_printpatches then
       print_patch env sigma n patch
     else
       Printf.printf "Defined %s\n" n
  | None -> ()
          
(* Common inversion functionality *)
let invert_patch n env patch sigma (define, last_def) =
  let sigma, inverted = invert_terms invert_factor env [patch] sigma in
  try
    let patch_inv = List.hd inverted in
    let sigma, _ = infer_type env sigma patch_inv in
    let definition = define n env sigma patch_inv last_def in
    let n_string = Option.map Id.to_string n in
    debug_print_patch env sigma n_string patch_inv;
    definition
  with _ ->
    failwith "Could not find a well-typed inverted term"

(* Common patch command functionality *)
    
let patch env n try_invert a search sigma (define, last_def) =
  let reduce = try_reduce reduce_remove_identities in
  let sigma, patch_to_red = search env a sigma in
  let sigma, patch = reduce env sigma patch_to_red in
  let prefix = Option.map Id.to_string n in
  let next_def = define n env sigma patch last_def in
  debug_print_patch env sigma prefix patch;
  if try_invert then
    try
      let inv_n_string = Option.map (fun x -> x ^ "_inv") prefix in
      let inv_n = Option.map Id.of_string inv_n_string in
      invert_patch inv_n env patch sigma (define, next_def)
    with _ ->
      next_def
  else
    next_def


(* Defines a patch as a new hypothesis. *)
let patch_def_hypothesis =  
  ((fun n _ sigma patch last_def ->
    Proofview.tclTHEN last_def
      (letin_pat_tac false None (Names.Name (Option.get n))
         (sigma, EConstr.of_constr patch) Locusops.nowhere)),
   Tacticals.New.tclIDTAC)
  
(* Suggest something to do with the generated patch. *)
let patch_suggest =
  ((fun _ env sigma patch last_def ->
    let typ = (Typeops.infer env patch).uj_type in
    let type_s = Printer.pr_constr_env env sigma typ in
    let asrt = str "assert " ++ type_s ++ str ".\n" in
    let tacs = tac_from_term env sigma patch in
    Feedback.msg_info (asrt ++ tac_to_string sigma tacs);
    last_def),
   Tacticals.New.tclIDTAC)
  
(* Defines a patch globally. *)
let patch_def_global =
  ((fun n _ sigma patch _ ->
    ignore (define_term (Option.get n) sigma patch false)), ())
  
  
(* --- Commands --- *)

(*
 * Command functionality for generating reusable patches
 * Patch Proof, Patch Definition, and Patch Constructor all call this
 * The latter two just pass extra guidance for now
 *)

let patch_proof n d_old d_new cut intern =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, (old_term, new_term) = intern env d_old d_new sigma in
  let sigma, (d, opts) = configure env old_term new_term cut sigma in
  let change = get_change opts in
  let try_invert = not (is_conclusion change || is_hypothesis change) in
  let search _ _ = search_for_patch old_term opts d in
  patch env n try_invert () search sigma

(* Tactic to test decompilation of a single term into tactics. *)
let decompile_tactic trm =
  let (sigma, env) = Pfedit.get_current_context () in
  let trm = EConstr.to_constr sigma trm in
  let tacs = tac_from_term env sigma trm in
  Feedback.msg_info (tac_to_string sigma tacs);
  Tacticals.New.tclIDTAC

(* Decompiles a single term into a tactic list printed to console. *)
let decompile_command trm =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, trm = intern env sigma trm in
  let trm = unwrap_definition env trm in
  let tacs = tac_from_term env sigma trm in
  Feedback.msg_debug (tac_to_string sigma tacs) 
  
(* Convert constr's from patch tactics to appropriate term type. *)
let intern_tactic env d_old d_new sigma =
  (sigma, (unwrap_definition env (EConstr.to_constr sigma d_old),
           unwrap_definition env (EConstr.to_constr sigma d_new)))
  
(* Tactic which computes and names a patch as a new hypothesis. *)
let patch_proof_tactic n d_old d_new =
  patch_proof (Some n) d_old d_new None intern_tactic patch_def_hypothesis

(* Tactic which computes a patch and suggests what to do with it. *)
let suggest_patch_tactic d_old d_new =
  patch_proof None d_old d_new None intern_tactic patch_suggest
  
(* Command which computes a patch as a global name. *)
let patch_proof_command n d_old d_new cut =
  patch_proof (Some n) d_old d_new cut intern_defs patch_def_global 
  
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
  let sigma, (d, opts) = configure_optimize env trm sigma in
  let search _ _ = search_for_patch trm opts d in
  patch env (Some n) false () search sigma patch_def_global

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
  in patch env (Some n) false t search sigma patch_def_global

(* Invert a term *)
let invert n trm : unit =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, def = intern env sigma trm in
  let body = lookup_definition env def in
  invert_patch (Some n) env body sigma patch_def_global

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

              
(* --- Tactic syntax --- *)

TACTIC EXTEND patch_tactic
| [ "patch" constr(d_old) constr(d_new) "as" ident(n) ] ->
   [ patch_proof_tactic n d_old d_new ]
END

TACTIC EXTEND suggest_tactic
| [ "suggest" "patch" constr(d_old) constr(d_new) ] ->
   [ suggest_patch_tactic d_old d_new ]
END

TACTIC EXTEND decompile
| [ "decompile" constr(trm) ] ->
   [ decompile_tactic trm ]
END

(* --- Vernac syntax --- *)

(* Decompile Command *)
VERNAC COMMAND EXTEND Decompile CLASSIFIED AS SIDEFF
| [ "Decompile" constr(trm) ] ->
   [ decompile_command trm ]
END

(* Patch command *)
VERNAC COMMAND EXTEND PatchProof CLASSIFIED AS SIDEFF
| [ "Patch" "Proof" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ patch_proof_command n d_old d_new None ]
| [ "Patch" "Proof" constr(d_old) constr(d_new) "cut" "by" constr(cut) "as" ident(n)] ->
  [ patch_proof_command n d_old d_new (Some cut) ]
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

(* Replace subterms with a convertible term *)
VERNAC COMMAND EXTEND ReplaceConvertible CLASSIFIED AS SIDEFF
| [ "Replace" "Convertible" constr_list(conv_trms) "in" constr(def) "as" ident(n) ] ->
  [ do_replace_convertible n conv_trms def ]
| [ "Replace" "Convertible" "Module" constr_list(conv_trms) "in" reference(mod_ref) "as" ident(n) ] ->
  [ do_replace_convertible_module n conv_trms mod_ref ]
END
