open Environ
open Constr
open Evd
open Stateutils
open Names
open Constrexpr
open Libnames

(*
 * Refactoring functionality
 *)

(* --- Internal functionality (no side-effects) --- *)

(*
 * Find all subterms of the second term convertible with anything in the list of * the first terms, and replace all of those with the appropriate element from
 * the list itself. Do the replacements from left to right in the list.
 *
 * Optionally, also generate correctness proof.
 *)
val replace_convertible :
  bool -> (* generate proofs *)
  env -> (* environment *)
  constr list -> (* what to replace *)
  constr -> (* term to replace subterms within *)
  evar_map -> (* state *)
  (constr * (constr * constr) option) state (* new term & proof/proof type *)

(* --- External functionality (side-effects) --- *)

(*
 * Do replace_convertible and define new terms in the global environment
 *)
val do_replace_convertible :
  Id.t -> (* name of new definition *)
  constr_expr list -> (* what to replace *)
  constr_expr -> (* term to replace subterms within *)
  unit

(*
 * Do replace_convertible, but over an entire module, and define a new
 * module with the updated terms
 *)
val do_replace_convertible_module :
  Id.t -> (* name of new module *)
  constr_expr list -> (* what to replace *)
  reference -> (* reference to module to replace subterms of terms within *)
  unit
