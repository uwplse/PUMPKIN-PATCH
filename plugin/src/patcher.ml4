DECLARE PLUGIN "patch"

open Constr
open Names
open Environ
open Coqterms
open Assumptions
open Evaluation
open Proofdiff
open Search
open Printing
open Inverting
open Theorem
open Abstraction
open Abstractionconfig
open Searchopts
open Reducers
open Specialization
open Factoring
open Collections
open Cutlemma
open Kindofchange
open Changedetectors
open Stdarg

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
let intern_defs d1 d2 : types * types =
  let (evm, env) = Pfedit.get_current_context() in
  let d1 = intern env evm d1 in
  let d2 = intern env evm d2 in
  (unwrap_definition env d1, unwrap_definition env d2)

(* Initialize diff & search configuration *)
let configure trm1 trm2 cut : goal_proof_diff * options =
  let (evm, env) = Pfedit.get_current_context() in
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
    ignore (define_term n evm patch_inv false);
    let n_string = Id.to_string n in
    if !opt_printpatches then
      print_patch env evm n_string patch_inv
    else
      Printf.printf "Defined %s\n" (Id.to_string n)
  with _ ->
    failwith "Could not find a well-typed inverted term"

(* Common patch command functionality *)
let patch n old_term new_term try_invert a search =
  let (evm, env) = Pfedit.get_current_context () in
  let reduce = try_reduce reduce_remove_identities in
  let patch = reduce env (search env evm a) in
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

(*
 * Translate each fix or match subterm into an equivalent application of an
 * eliminator, defining the new term with the given name.
 *
 * Mutual fix or cofix subterms are not supported.
 * (By Nate Yazdani, from DEVOID)
 *)
let do_desugar_constant ident const_ref =
  ignore
    begin
      qualid_of_reference const_ref |> Nametab.locate_constant |>
      Global.lookup_constant |> transform_constant ident desugar_constr
    end

(*
 * Translate fix and match expressions into eliminations, as in
 * do_desugar_constant, compositionally throughout a whole module.
 *
 * The optional argument is a list of constants outside the module to include
 * in the translated module as if they were components in the input module.
 * (By Nate Yazdani, from DEVOID)
 *)
let do_desugar_module ?(incl=[]) ident mod_ref =
  let open Util in
  let consts = List.map (qualid_of_reference %> Nametab.locate_constant) incl in
  let include_constant subst const =
    let ident = Label.to_id (Constant.label const) in
    let tr_constr env evm = subst_globals subst %> desugar_constr env evm in
    let const' =
      Global.lookup_constant const |> transform_constant ident tr_constr
    in
    Globmap.add (ConstRef const) (ConstRef const') subst
  in
  let init () = List.fold_left include_constant Globmap.empty consts in
  ignore
    begin
      qualid_of_reference mod_ref |> Nametab.locate_module |>
      Global.lookup_module |> transform_module_structure ~init ident desugar_constr
    end

(* --- Commands --- *)

(*
 * Command functionality for generating reusable patches
 * Patch Proof, Patch Definition, and Patch Constructor all call this
 * The latter two just pass extra guidance for now
 *)
let patch_proof n d_old d_new cut =
  let (old_term, new_term) = intern_defs d_old d_new in
  let (d, opts) = configure old_term new_term cut in
  let change = get_change opts in
  let try_invert = not (is_conclusion change || is_hypothesis change) in
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
  let (evm, env) = Pfedit.get_current_context() in
  let (old_term, new_term) = (intern env evm d_old, intern env evm d_new) in
  patch n old_term new_term false t
    (fun env evm t ->
      let theorem = intern env evm t in
      let t_trm = lookup_definition env theorem in
      update_theorem env old_term new_term t_trm)

(* Invert a term *)
let invert n trm : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let body = lookup_definition env (intern env evm trm) in
  invert_patch n env evm body

(* Specialize a term *)
let specialize n trm : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let reducer = specialize_body specialize_term in
  let specialized = reducer env (intern env evm trm) in
  ignore (define_term n evm specialized false)

(* Abstract a term by a function or arguments *)
let abstract n trm goal : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let c = lookup_definition env (intern env evm trm) in
  let goal_type = unwrap_definition env (intern env evm goal) in
  let config = configure_from_goal env goal_type c in
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
      let reduced = reduce_term config.env app in
      let reconstructed = reconstruct_lambda config.env reduced in
      ignore (define_term n evm reconstructed false)
  else
    failwith "Failed to abstract"

(* Factor a term into a sequence of lemmas *)
let factor n trm : unit =
  let (evm, env) = Pfedit.get_current_context() in
  let body = lookup_definition env (intern env evm trm) in
  let fs = reconstruct_factors (factor_term env body) in
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

(* Desugar any/all fix/match subterms into eliminator applications *)
VERNAC COMMAND EXTEND TranslateMatch CLASSIFIED AS SIDEFF
| [ "Preprocess" reference(const_ref) "as" ident(id) ] ->
  [ do_desugar_constant id const_ref ]
| [ "Preprocess" "Module" reference(mod_ref) "as" ident(id) ] ->
  [ do_desugar_module id mod_ref ]
| [ "Preprocess" "Module" reference(mod_ref) "as" ident(id) "{" "include" ne_reference_list_sep(incl_refs, ",") "}" ] ->
  [ do_desugar_module ~incl:incl_refs id mod_ref ]
END
