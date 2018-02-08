open Environ
open Context
open Declarations
open Term
open Names

type 'a contextual = env -> 'a

(* --- General environment management auxiliary functions --- *)

(* Look up all indexes from a list in an environment *)
val lookup_rels : int list -> env -> Rel.Declaration.t list

(* Return a list of all indexes in an environment, starting with 1 *)
val all_rel_indexes : env -> int list

(* Return a list of all bindings in an environment, starting with the closest *)
val lookup_all_rels : env -> Rel.Declaration.t list

(* Push a new local assumption onto the environment *)
val assume_rel : env -> name -> types -> env

(* Push something to the highest position in an environment *)
val push_last : Rel.Declaration.t -> env -> env

(* --- Getting bindings for terms --- *)

(*
 * Inductive types create bindings that we need to push to the environment
 * This function gets those bindings
 *)
val bindings_for_inductive : env -> mutual_inductive_body -> one_inductive_body list -> Rel.Declaration.t list

(*
 * A fixpoint also creates bindings that we need to push to the environment
 * This function gets all of those bindings
 *)
val bindings_for_fix : name array -> types array -> Rel.Declaration.t list

(* --- Helper functions for names --- *)

(*
 * Join two binding names, preserving a string identifier if consistent between
 * the two names.
 *)
val join_names : name -> name -> name
