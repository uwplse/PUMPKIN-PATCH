(* Logic for proof categories that is specific to terms and types *)

open Constr
open Environ
open Proofcat
open Names
open Evd
open Stateutils

(* --- Construction --- *)

(* Get the extension for a term in an environment *)
val ext_of_term : env -> types -> extension

(* Get a fresh inductive hypothesis *)
val fresh_ih : unit -> extension

(* --- Destruction --- *)

(*
 * Get the term from an extension
 * Fail if the extension is anonymous and thus has no term
 *)
val ext_term : extension -> types

(* Check whether an extension represents a lambda term *)
val ext_is_lambda : extension -> bool

(* Check whether an extension represents an inductive hypothesis *)
val ext_is_ih : extension -> bool

(*
 * Get the environment from a context
 * Fails if the context is the initial context,
 * which for now does not have an associated environment
 *)
val context_env : context_object -> env

(*
 * Get the new term from a context
 * Fails if the context is the initial context
 *)
val context_term : context_object -> types

(*
 * Destruct a context that is an old context extended by term
 * Fail if the context is the initial context
 *)
val dest_context_term : context_object -> types * env

(* Get the index of a context *)
val context_index : context_object -> int

(* Check whether a context is extended by a term representing a product *)
val context_is_product : context_object -> bool

(*
 * Get the product type for a context
 * Fail if the context is the initial context
 * Fail if the context is extended with a term that is not a product
 *)
val context_as_product : context_object -> Name.t * types * types

(* Check whether a context is extended by a term represent an application *)
val context_is_app : context_object -> bool

(*
 * Get the function and args for a context
 * Fail if the context is the initial context
 * Fail if the context is extended with a term that is not an application
 *)
val context_as_app  : context_object -> types * types array

(*
 * From a proof category that represents an inductive proof, get
 * the inductive parameters
 *
 * This assumes the proof category represents an inductive proof
 * It has undefined behavior if you call it otherwise
 *)
val params : proof_cat -> int -> evar_map -> (arrow list) state

(*
 * From a proof category that represents an inductive proof, get
 * the inductive property
 *
 * This assumes the proof category represents an inductive proof
 * It has undefined behavior if you call it otherwise
 *)
val prop : proof_cat -> int -> evar_map -> arrow state

(*
 * Get the only extension in a proof category as a term
 * Fail if there are no extensions
 * Fail if there are multiple extensions
 *)
val only_extension_as_term : proof_cat -> types

(*
 * Given a proof category with several paths,
 * construct several proof categories, each with one path.
 *)
val split : proof_cat -> evar_map -> (proof_cat list) state

(* --- Transformations on terms and environments --- *)

(*
 * Curry a lambda extension
 * Fail if it is not a lambda
 *)
val curry_lambda : extension -> extension

(* --- Finding terms and environments  --- *)

(* Check if a proof category has an inductive hypothesis *)
val has_ihs : proof_cat -> bool

(* Find the inductive hypotheses in a proof category *)
val find_ihs : proof_cat -> arrow list

(*
 * Compare two arrows and determine which is closer to an IH
 * When they are equidistant, prefer ones that are lower in the proof
 * The IHs are only supplied for efficiency, you can get them with find_ihs
 *)
val closer_to_ih : proof_cat -> arrow list -> arrow -> arrow -> evar_map -> int state

(*
 * Sort a list of proof_cats so that the base cases are first in the list
 *)
val base_cases_first : proof_cat list -> proof_cat list

(* --- Debruijn --- *)

(* Unshifts the index of an extension if it is not locally bound *)
val unshift_ext_local : int -> int -> extension -> extension

(* Unshifts the index of an extension *)
val unshift_ext_by : int -> extension -> extension

(* Shifts the index of an extension *)
val shift_ext_by : int -> extension -> extension

(* --- Substitution --- *)

(* Substitute in an environment for the environment in an extension *)
val substitute_ext_env : env -> extension -> extension

(*
 * Substitute in an expanded version of the terminal object
 * The first proof_cat is the original proof_cat
 * The second proof_cat should replace the terminal object in the original
 * This is commonly used to update categories after expansion
 *)
val substitute_terminal : proof_cat -> proof_cat -> evar_map -> proof_cat state

(* --- Merging categories --- *)

(*
 * Substitute a source category (first) into a destination category (second)
 * That is, substitutes the terminal object for the initial object
 * Assumes that the source has a terminal object
 * Assumes that the destination has an initial object
 * Assumes contexts are not equal (creates fresh identifiers)
 *)
val substitute_categories : proof_cat -> proof_cat -> evar_map -> proof_cat state

(*
 * Find the context where the shortest path is a given length
 * Errors if more than one such context exists
 * Assumes there is an initial object
 *)
val context_at_index : proof_cat -> int -> context_object

(*
 * Assume the first n objects in a category are equal, and merge
 * any objects at that index
 * Assume the category has an initial object
 *)
val merge_up_to_index : int -> proof_cat -> proof_cat

(*
 * Merge an inductive type
 * The bool says whether the inductive type is recursive
 * The int is the number of parameters for the inductive type
 * If the type is recursive, just merge the parameters
 * Otherwise, merge the parameters and also the conclusions
 *)
val merge_inductive : bool -> int -> proof_cat -> proof_cat

(* --- Binding --- *)

(*
 * Bind two contexts in c with the provided extension
 * If an arrow between those contexts with an anonymous binding exists,
 * then substitute the provided extension
 * Otherwise, add the new binding
 *)
val bind : proof_cat -> arrow -> proof_cat

(*
 * Build a function application for the last extension in a proof category
 * The provided extension holds the function before it is applied
 * Apply that to the provided number most recent local bindings
 *)
val bind_apply_function : extension -> int -> proof_cat -> proof_cat

(*
 * Bind an array of arguments to each category in an array of categories,
 * where each category in the array is an inductive constructor,
 * and each argument is an argument to the respective constructor
 *)
val bind_inductive_args : types array -> proof_cat array -> proof_cat array

(*
 * Bind an inductive property and inductive parameters
 * to a proof category for an inductive proof
 *
 * Pass the total number of possible params in an int
 *)
val bind_property_and_params :
  types option -> types list -> int -> proof_cat -> proof_cat

