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
open Constrarg
open Substitution
open Printing
open Inverting
open Theorem
open Abstracters
open Abstraction
open Abstractionconfig
open Debruijn
open Searchopts
open Reducers
open Specialization
open Factoring
open Collections
open Coqenvs
open Cutlemma
open Kindofchange
open Changedetectors

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
  Goptions.optsync = true;
  Goptions.optdepr = false;
  Goptions.optname = "Print patches PUMPKIN finds";
  Goptions.optkey = ["PUMPKIN"; "Printing"];
  Goptions.optread = (fun () -> !opt_printpatches);
  Goptions.optwrite = (fun b -> opt_printpatches := b);
}

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
  let change = find_kind_of_change lemma d in
  (d, configure_search d change lemma)

(* Common inversion functionality *)
let invert_patch n env evm patch =
  let inverted = invert_terms invert_factor env [patch] in
  try
    let patch_inv = List.hd inverted in
    let _ = infer_type env patch_inv in
    define_term n env evm patch_inv;
    let n_string = Id.to_string n in
    if !opt_printpatches then
      print_patch env evm n_string patch_inv
    else
      Printf.printf "Defined %s\n" (Id.to_string n)
  with _ ->
    failwith "Could not find a well-typed inverted term"

(* Common patch command functionality *)
let patch n old_term new_term try_invert a search =
  let (evm, env) = Lemmas.get_current_context() in
  let reduce = try_reduce reduce_remove_identities in
  let patch = reduce env (search env evm a) in
  let prefix = Id.to_string n in
  define_term n env evm patch;
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
  let specialized = reducer env (intern env evm trm) in
  define_term n env evm specialized

(* Abstract a term by a function or arguments *)
let abstract n trm goal : unit =
  let (evm, env) = Lemmas.get_current_context() in
  let c = lookup_definition env (intern env evm trm) in
  let goal_type = unwrap_definition env (intern env evm goal) in
  let config = configure_from_goal env goal_type c in
  let abstracted = abstract_with_strategies config in
  if List.length abstracted > 0 then
    try
      define_term n env evm (List.hd abstracted)
    with _ -> (* Temporary, hack to support arguments *)
      let num_args = List.length (config.args_base) in
      let num_discard = nb_rel config.env - num_args in
      let rels = List.map (fun i -> i + num_discard) (from_one_to num_args) in
      let args = Array.map (fun i -> mkRel i) (Array.of_list rels) in
      let app = mkApp (List.hd abstracted, args) in
      let reduced = reduce_term config.env app in
      let reconstructed = reconstruct_lambda config.env reduced in
      define_term n env evm reconstructed
  else
    failwith "Failed to abstract"

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

let register_tactic n tac typs =
  let (evm, env) = Lemmas.get_current_context() in
  let pat = List.map (intern env evm) typs in
  let tag = Id.to_string n in
  try
    Usertactics.register_tactic tag (Tacinterp.interp tac) pat;
    Printf.printf "Registered patch tactic '%s'\n" tag
  with Registry.Registry_collision ->
       Printf.printf "A patch tactic is already registered as '%s'\n" tag
     | _ ->
       Printf.printf "Failed to register patch tactic '%s'\n" tag

let unregister_tactic n =
  let tag = Id.to_string n in
  Usertactics.unregister_tactic tag;
  Printf.printf "Unregistered patch tactic '%s'\n" tag

let register_lemma trm =
  let (evm, env) = Lemmas.get_current_context() in
  let lem = intern env evm trm in
  try
    let Some tag = ident_of_term lem in
    try
      Userlemmas.register_lemma tag lem;
      Printf.printf "Registered patch lemma '%s'\n" tag
    with
    | Registry.Registry_collision ->
      Printf.printf "A patch lemma is already registered as '%s'\n" tag
    | _ ->
      Printf.printf "Failed to register patch lemma '%s'\n" tag
  with Match_failure (_, _, _) ->
    Printf.printf "A patch lemma must be a global constant\n"

let unregister_lemma trm =
  let (evm, env) = Lemmas.get_current_context() in
  let lem = intern env evm trm in
  try
    let Some tag = ident_of_term lem in
    Userlemmas.unregister_lemma tag;
    Printf.printf "Unregistered patch lemma '%s'\n" tag
  with Match_failure (_, _, _) ->
    Printf.printf "A patch lemma must be a global constant\n"

(* Decide a proposition with the named tactic *)
let decide_with n typ n_tac : unit =
  let (evm, env) = Lemmas.get_current_context() in
  let s_tac = Id.to_string n_tac in
  try
    let pf = Usertactics.call_tactic env evm (intern env evm typ) s_tac in
    define_term n env evm pf
  with Usertactics.Tactic_failure ->
       Printf.printf "Patch tactic '%s' could not decide goal\n" s_tac;;

(* Decide a proposition with any applicable tactic *)
let decide n typ : unit =
  let (evm, env) = Lemmas.get_current_context() in
  match Usertactics.try_tactics env evm (intern env evm typ) with
  | Some pf -> define_term n env evm pf
  | None -> Printf.printf "Patch tactics could not decide goal\n";;

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

(* Register a patch tactic or lemma *)
VERNAC COMMAND EXTEND RegisterTactic CLASSIFIED AS SIDEFF
| [ "Register" "Patch" "Tactic" tactic(tac) "as" ident(n) "for" constr_list(typs) ] ->
  [ register_tactic n tac typs ]
| [ "Register" "Patch" "Lemma" constr(lem) ] ->
  [ register_lemma lem ]
END

(* Unregister a patch tactic or lemma *)
VERNAC COMMAND EXTEND UnregisterTactic CLASSIFIED AS SIDEFF
| [ "Unregister" "Patch" "Tactic" ident(n) ] ->
  [ unregister_tactic n ]
| [ "Unregister" "Patch" "Lemma" constr(lem) ] ->
  [ unregister_lemma lem ]
END

(* Decide the proof of a proposition with tactics *)
VERNAC COMMAND EXTEND DecideProof CLASSIFIED AS SIDEFF
| [ "Decide" constr(typ) "with" ident(n_tac) "as" ident(n) ] ->
  [ decide_with n typ n_tac ]
| [ "Decide" constr(typ) "as" ident(n) ] ->
  [ decide n typ ]
END
