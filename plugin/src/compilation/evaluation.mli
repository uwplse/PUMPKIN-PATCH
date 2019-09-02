(* --- Evaluation, which is lazy (takes one step) --- *)

open Constr
open Environ
open Proofcat
open Declarations
open Stateutils
open Evd

(*
 * Evaluate a term one step in an environment
 * Then bind the single anonymous arrow to the extension
 *)
val eval_theorem_bind : extension -> env -> types -> evar_map -> proof_cat state

(* Evaluate an anonymous proof (inhabitant) of a theorem (type) one step *)
val eval_theorem : env -> types -> evar_map -> proof_cat state

(* Evaluate a proof (term) one step *)
val eval_proof : env -> types -> evar_map -> proof_cat state

(* Evaluate an arrow as a proof *)
val eval_proof_arrow : arrow -> evar_map -> proof_cat state

(*
 * Evaluate an inductive proof given:
 * 1. The inductive type that the proof inducts over
 * 2. An expanded proof_cat for the induction principle
 * 3. The arguments to the induction principle
 * 4. Other arguments that may be leftover after induction
 *
 * Bind the arguments to the application of the induction principle
 * Return the number of params and any leftover arguments after induction
 *)
val eval_induction :
  mutual_inductive_body -> proof_cat -> types array -> proof_cat * int * types list
