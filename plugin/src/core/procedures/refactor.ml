open Envutils
open Substitution
open Stateutils
open Convertibility
open Inference
open Equtils
open Indutils
open Defutils
open Constr
open Transform
open Global
open Nametab
open Nameutils
open Declarations
open Names
open Pp

(*
 * Refactoring functionality
 *)

(* --- Options --- *)

let opt_prove_replace_correct = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate correctness proofs for replace convertibile";
  Goptions.optkey = ["PUMPKIN"; "Prove"; "Replace"];
  Goptions.optread = (fun () -> !opt_prove_replace_correct);
  Goptions.optwrite = (fun b -> opt_prove_replace_correct := b);        
}

(* --- Correctness proofs --- *)

(* 
 * Prove coherence with the components search finds
 * Return the coherence proof term and its type
 *)
let maybe_prove_replace_correct prove_correct env trm sub =
  if prove_correct then
    branch_state
      (fun (trm, sub) sigma -> convertible env sigma trm sub)
      (fun (trm, sub) sigma ->
        let sigma, typ = infer_type env sigma trm in
        let refl = apply_eq_refl { typ; trm } in
        let refl_typ = apply_eq { at_type = typ; trm1 = trm; trm2 = sub} in
        ret (Some (refl, refl_typ)) sigma)
      (fun (trm, sub) ->
        (* not yet implemented *)
        ret None)
      (trm, sub)
  else
    ret None

(* --- Top-level refactoring functions --- *)

(* Replace all subterms convertible with conv_trms in trm *)
let replace_convertible prove_correct env conv_trms trm sigma =
  let trm = unwrap_definition env trm in
  let sigma, sub =
    fold_right_state
      (fun conv_trm trm sigma ->
        all_conv_substs env sigma (conv_trm, conv_trm) trm)
      conv_trms
      trm
      sigma
  in
  let sigma, pf = maybe_prove_replace_correct prove_correct env trm sub sigma in
  sigma, (sub, pf)

(* --- Command implementations with side effects --- *)

(* Top-level Replace Convertible implementation *)
let do_replace_convertible n convs def =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, convs =
    map_state (fun conv sigma -> intern env sigma conv) convs sigma
  in
  let sigma, def = intern env sigma def in
  let prove = !opt_prove_replace_correct in
  let pf_ref = ref None in
  (match kind def with
  | Ind (i, u) ->
     let mind_body = lookup_mind (fst i) in
     check_inductive_supported mind_body;
     let ind_body = mind_body.mind_packets.(0) in
     let mind_consnames =
       Array.map
         (fun id -> Nameops.add_suffix id "'") (* for now, hardcoded *)
         ind_body.mind_consnames
     in
     let ind_body' = { ind_body with mind_consnames } in  
     let _ =
       transform_inductive
         n
         (fun env sigma def ->
           let sigma, (sub, pf) =
             replace_convertible false env convs def sigma
           in sigma, sub)
         (mind_body, ind_body')
     in
     Feedback.msg_notice (str "Defined " ++ str (Id.to_string n) ++ str "\n")
  | _ ->
     let sigma, (sub, pf) = replace_convertible prove env convs def sigma in
     pf_ref := pf;
     ignore (define_term n sigma sub false);
     Feedback.msg_notice (str "Defined " ++ str (Id.to_string n) ++ str "\n"));
  if prove then
    if Option.has_some (!pf_ref) then
      let pf_n = with_suffix n "correct" in
      let pf_trm, pf_typ = Option.get (!pf_ref) in
      let _ = define_term ~typ:pf_typ pf_n sigma pf_trm true in
      Feedback.msg_notice
        (str "Defined " ++ str (Id.to_string pf_n) ++ str ("\n"))
    else
      Feedback.msg_warning
        (str "Could not find correctness proof---may not yet be implemented")
  else
    ()        

(*
 * Same as replace_convertible, but over an entire module, replacing
 * terms later in the module with renamed versions
 *)
let do_replace_convertible_module n convs mod_ref : unit =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, convs =
    map_state (fun conv sigma -> intern env sigma conv) convs sigma
  in
  let prove = !opt_prove_replace_correct in
  (if prove then
     Feedback.msg_warning
       (str "Correctness proofs for whole module replace not yet supported")
   else
     ());
  let replace_in_term env sigma def =
    let sigma, (sub, pf) = replace_convertible false env convs def sigma in
    sigma, sub
  in
  let m = lookup_module (locate_module mod_ref) in
  ignore (transform_module_structure n replace_in_term m)
