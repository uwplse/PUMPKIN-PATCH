open Environ
open Context
open Declarations
open Term
open Names

type 'a contextual = env -> 'a

(* --- General environment management auxiliary functions --- *)

(* Look up all indexes from a list in an environment *)
val lookup_rels : int list -> env -> rel_declaration list

(* Return a list of all indexes in an environment, starting with 1 *)
val all_rel_indexes : env -> int list

(* Return a list of all bindings in an environment, starting with the closest *)
val lookup_all_rels : env -> rel_declaration list

(* Push something to the highest position in an environment *)
val push_last : rel_declaration -> env -> env

(* --- Getting bindings for terms --- *)

(*
 * Inductive types create bindings that we need to push to the environment
 * This function gets those bindings
 *)
val bindings_for_inductive : env -> mutual_inductive_body -> one_inductive_body list -> rel_declaration list

(*
 * A fixpoint also creates bindings that we need to push to the environment
 * This function gets all of those bindings
 *)
val bindings_for_fix : name array -> types array -> rel_declaration list
