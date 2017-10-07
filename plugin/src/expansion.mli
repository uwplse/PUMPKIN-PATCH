(* Expanding proof categories *)

open Names
open Environ
open Term
open Proofcat

(* --- Type definitions --- *)

type 'a expansion_strategy = 'a -> 'a

(* --- Terms and types ---*)

(* TODO hide me when refactoring is done *)
val expand_product : env -> (Name.t * types * types) -> proof_cat

(* --- Contexts --- *)

(*
 * Expand a term exactly once
 * Default to using the provided function when it cannot be expanded further
 * Error if the type context doesn't hold any terms
 *)
val expand_term : (env -> types -> proof_cat) -> context_object -> proof_cat

(*
 * Expand a product type as far as its conclusion goes
 * Error if the type context doesn't hold any terms
 * Error if the type context isn't newly extended with a product type
 *)
val expand_product_fully : context_object -> proof_cat

(* --- Categories --- *)

(*
 * Expand the terminal object of a proof category exactly once
 * Return the original category if it cannot be exapnded
 *)
val expand_terminal : proof_cat expansion_strategy

(*
 * Expand all parameters of an inductive proof
 * Also expand out the node with the induction principle
 * Provide the number of parameters to expand
  *)
val expand_inductive_params : int -> proof_cat expansion_strategy

(*
 * Expand an inductive constructor
 * That is, expand its conclusion fully if it is dependent
 * Then mark the edges that are inductive hypotheses
 *)
val expand_constr : proof_cat expansion_strategy
