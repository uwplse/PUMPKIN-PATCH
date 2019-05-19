(* Simple auxiliary functions for Coq terms *)

open Environ
open Evd
open Constr
open Declarations
open Names

(* Auxiliary types *)

type closure = env * (types list)

(* --- Representations --- *)

(* Internalize *)
val intern : env -> evar_map -> Constrexpr.constr_expr -> types

(* Externalize *)
val extern : env -> evar_map -> types -> Constrexpr.constr_expr

(* Convert an external reference into a qualid *)
val qualid_of_reference : Libnames.reference -> Libnames.qualid
                                           
(* --- Terms --- *)

(*
 * Define a new Coq term
 * Refresh universes if the bool is true, otherwise don't
 * (Refreshing universes is REALLY costly)
 *)
val define_term : Id.t -> evar_map -> types -> bool -> global_reference

(* Get the Coq identity term for a type *)
val identity_term : env -> types -> types

(* Get the substitution term *)
val eq_ind : types

(* Get the reverse substitution term *)
val eq_ind_r : types

(* Get the symmetry term for equality *)
val eq_sym : types

(*
 * Check if a term is Prop
 *)
val is_prop : types -> bool

(*
 * Check if a term is a rewrite via eq_ind or eq_ind_r
 * For efficiency, don't consider convertible terms
 *)
val is_rewrite : types -> bool

(*
 * Determine if a term applies an identity term
 * For efficiency, don't consider convertible terms
 *)
val applies_identity : types -> bool

(* Lookup a definition in an environment *)
val lookup_definition : env -> types -> types

(*
 * Lookup a definition in an environment
 * If the result is a definition, continue looking it up until it's not
 * Return the original term if it is not a definition at all
 *)
val unwrap_definition : env -> types -> types

(* Zoom all the way into a lambda term *)
val zoom_lambda_term : env -> types -> env * types

(* Reconstruct a lambda from an environment to some body *)
val reconstruct_lambda : env -> types -> types

(* Reconstruct a product from an environment to some body *)
val reconstruct_prod : env -> types -> types

(* --- Inductive types --- *)

(* (To avoid confusing Coq naming) get the body of a mutually inductive type *)
val lookup_mutind_body : MutInd.t -> env -> mutual_inductive_body

(* Get the type of a mutually inductive type *)
val type_of_inductive : env -> mutual_inductive_body -> one_inductive_body -> types

(*
 * Error if the type is mutually inductive or coinductive
 * Remove calls to this when we implement support for these types
 *)
val check_inductive_supported : mutual_inductive_body -> unit

(*
 * Check if a constant is an inductive elminator
 * If so, return Some with the inductive type
 * Otherwise, return None
 *)
val inductive_of_elim : env -> pconstant -> MutInd.t option

(*
 * Get the number of constructors for an inductive type
 *)
val num_constrs : mutual_inductive_body -> int
                                             
(* --- Modules --- *)

(*
 * Pull any functor parameters off the module signature, returning the list of
 * functor parameters and the list of module elements (i.e., fields).
 *)
val decompose_module_signature : module_signature -> (Names.MBId.t * module_type_body) list * structure_body

(*
 * Declare an interactive (i.e., elementwise) module structure, with the
 * functional argument called to populate the module elements by declaration.
 *
 * The optional argument specifies functor parameters.
 *)
val declare_module_structure :
  ?params:(Constrexpr.module_ast Declaremods.module_params) ->
  Names.Id.t -> (unit -> unit) -> ModPath.t

(* Type-sensitive transformation of terms *)
type constr_transformer = env -> evar_map ref -> constr -> constr

(*
 * Declare a new constant under the given name with the transformed term and
 * type from the given constant.
 *
 * NOTE: Global side effects.
 *)
val transform_constant : Id.t -> constr_transformer -> constant_body -> Constant.t

(* --- Convertibility of terms --- *)

(* For now, these ignore universe inconsistency instead of dealing with it. *)

(* Checks whether two terms are convertible in an env with the empty evar environment *)
val convertible : env -> types -> types -> bool

(* Checks whether two terms are convertible in an env with evars *)
val convertible_e : env -> evar_map -> types -> types -> bool

(*
 * Checks whether the conclusions of two dependent types are convertible,
 * modulo the assumption that every argument we encounter is equal when
 * the types of those arguments are convertible. Expect exactly the same
 * number of arguments in the same order.
 *
 * For example, the following are true:
 *    concls_convertible empty (forall (a : nat), a) (forall (a : nat) b, a)
 *    concls_convertible empty (forall (a : nat), a) (forall (a : nat), a)
 *    concls_convertible empty (forall (a : nat), True) (forall (b : bin), True)
 *
 * The following are false:
 *    concls_convertible empty (forall a, True) False
 *    concls_convertible empty (forall a, True) True
 *    concls_convertible empty (forall (a : nat), a) (forall (a : bin), a)
 *    concls_convertible empty (forall a b, a) (forall a b, b)
 *
 * Assumes types are locally closed.
 *)
val concls_convertible : env -> types -> types -> bool

(*
 * Check whether all terms in two lists are convertible in an environment
 *)
val all_convertible : env -> types list -> types list -> bool

(*
 * Check whether all terms in two arrays of arguments are convertible in an
 * environment
 *)
val args_convertible : env -> types array -> types array -> bool

(*
 * Check whether the arguments to two applied functions are all convertible
 * in an environment.
 *
 * This fails with an error if the supplied terms are not applied functions.
 *)
val fun_args_convertible : env -> types -> types -> bool

(* --- Types of terms --- *)

(* Infer the type of a term in an environment, using Coq's unsafe type judgment *)
val infer_type : env -> types -> types

(* Check whether a term has a given type *)
val has_type : env -> types -> types -> bool

(* --- Convertibility of types --- *)

(* Checks whether the types of two terms are convertible in an env with the empty evar environment *)
val types_convertible : env -> types -> types -> bool

(* --- Existential variables --- *)

(* Terms with existential variables *)
type eterm = evar_map * types
type eterms = evar_map * (types array)

(* --- Auxiliary functions for dealing with two terms at once --- *)

(*type kind = (types, types) kind_of_term*)
val kinds_of_terms :
  (types * types) ->
  ((types, types, Sorts.t, Univ.Instance.t) kind_of_term * 
   (types, types, Sorts.t, Univ.Instance.t) kind_of_term)
