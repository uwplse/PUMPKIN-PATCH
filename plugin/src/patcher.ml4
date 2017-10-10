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
open Reversal
open Theorem
open Lifting
open Debruijn
open Searchopts
open Reduce

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

(*
 * Lookup the definitions, then apply a function to their difference
 *)
let apply_to_difference f (env : env) (d1 : types) (d2 : types) cut : 'a =
  let trm1 = unwrap_definition env d1 in
  let trm2 = unwrap_definition env d2 in
  let c1 = eval_proof env trm1 in
  let c2 = eval_proof env trm2 in
  let d = add_goals (difference c1 c2 no_assumptions) in
  let opts = configure_search d cut in
  f opts d

(* Common inversion functionality *)
let invert_patch n env evm patch =
  let inverted = invert_patches invert_patch env [patch] in
  try
    let patch_inv = List.hd inverted in
    let _ = infer_type env patch_inv in
    define_term n env evm patch_inv;
    Printf.printf "Defined %s\n" (Id.to_string n)
  with _ ->
    failwith "Could not find a well-typed inverted term"

(* Common patch command functionality *)
let patch n d_old d_new try_invert a search =
  let (evm, env) = Lemmas.get_current_context() in
  let old_term = intern env evm d_old in
  let new_term = intern env evm d_new in
  let patch = try_reduce env (search env evm old_term new_term a) in
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

(* The Patch Proof command functionality *)
let patch_proof n d_old d_new =
  patch n d_old d_new false ()
    (fun env evm old_term new_term _ ->
      let search = search_for_patch old_term in
      apply_to_difference search env old_term new_term None)

(* The Patch Definition command functionality *)
let patch_definition n d_old d_new cut =
  patch n d_old d_new true ()
    (fun env evm old_term new_term _ ->
      let cut_term = intern env evm cut in
      let lemma = build_cut_lemma env cut_term in
      let search = search_for_patch old_term in
      apply_to_difference search env old_term new_term (Some lemma))

(*
 * The Patch Theorem command functionality
 * This is an experimental dependent substitution command
 * It doesn't do search, so it's really not a patch finding procedure
 * It's also not a component
 * It just might be useful in the future, so feel free to play with it
 *)
let patch_theorem n d_old d_new t =
  patch n d_old d_new false t
    (fun env evm old_term new_term t ->
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
  define_term n env evm (specialize_term env (intern env evm trm))

(* Generalize a term to apply to all properties *)
(* TODO clean up and reconcile with other generalize_term function *)
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
         let lift_config = {is_concrete; env; args; cs; f_base; f_goal; strategies} in
         let lcs = lift_with_strategies lift_config in
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
  let path = find_type_path env body in
  let prefix = Id.to_string n in
  try
    List.iteri
      (fun i (en, t) ->
        let lemma = reconstruct_lambda en t in
        let lemma_id_string = String.concat "_" [prefix; string_of_int i] in
        let lemma_id = Id.of_string lemma_id_string in
        define_term lemma_id env evm lemma;
        Printf.printf "Defined %s\n" lemma_id_string)
      path
  with _ -> failwith "Could not find lemmas"

(* Patch command *)
VERNAC COMMAND EXTEND PatchProof CLASSIFIED AS SIDEFF
| [ "Patch" "Proof" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ patch_proof n d_old d_new ]
| [ "Patch" "Constructor" constr(d_old) constr(d_new) "cut" "by" constr(cut) "as" ident(n)] ->
  [ patch_definition n d_old d_new cut ]
| [ "Patch" "Definition" constr(d_old) constr(d_new) "cut" "by" constr(cut) "as" ident(n)] ->
  [ patch_definition n d_old d_new cut ]
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
