(*
 * Coq term and environment management
 *)

open Context
open Environ
open Constr
open Evd
open Constrexpr
open Names
open Declarations
open Globnames
open Decl_kinds

module Globmap = Globnames.Refmap
module Globset = Globnames.Refset

module CRD = Context.Rel.Declaration

(* --- Constants --- *)

val sigT : types
val existT : types
val sigT_rect : types
val projT1 : types
val projT2 : types
val eq : types
val eq_refl : types
val eq_ind : types
val eq_sym : types

(* --- Representations --- *)

(** Construct the external expression for a definition. *)
val expr_of_global : global_reference -> constr_expr

(*
 * Intern a term (for now, ignore the resulting evar_map)
 *)
val intern : env -> evar_map -> constr_expr -> types

(*
 * Extern a term
 *)
val extern : env -> evar_map -> types -> constr_expr

(*
 * Yves Bertot's edeclare, with extra optional type-checking call (see comment)
 *)
val edeclare :
  Id.t ->
  (locality * polymorphic * definition_object_kind) ->
  opaque:'a ->
  evar_map ->
  UState.universe_decl ->
  EConstr.constr ->
  EConstr.t option ->
  Impargs.manual_implicits ->
  global_reference Lemmas.declaration_hook ->
  bool ->
  global_reference

(*
 * Define a new Coq term
 * Refresh universes if the bool is true, otherwise don't
 * (Refreshing universes is REALLY costly)
 *)
val define_term : ?typ:types -> Id.t -> evar_map -> types -> bool -> global_reference

(*
 * Safely extract the body of a constant, instantiating any universe variables.
 * If needed, an evar_map should be constructed from the updated environment with
 * Evd.from_env.
 *
 * Raises a Match_failure if the constant does not exist.
 *)
val open_constant : env -> Constant.t -> env * constr

(* --- Constructing terms --- *)

(*
 * mkApp with a list (instead of an array) of arguments
 *)
val mkAppl : (types * types list) -> types

(*
 * Define a constant from an ID in the current path
 *)
val make_constant: Id.t -> types

(*
 * Ornament between products and lambdas, without changing anything else
 *)
val prod_to_lambda : types -> types
val lambda_to_prod : types -> types

(*
 * An application of eq
 *)
type eq_app =
  {
    at_type : types;
    trm1 : types;
    trm2 : types;
  }

(*
 * Convert between a term and an eq_app
 *)
val apply_eq : eq_app -> types
val dest_eq : types -> eq_app

(*
 * An application of eq_sym
 *)
type eq_sym_app =
  {
    eq_typ : eq_app;
    eq_proof : types;
  }

(*
 * Convert between a term and an eq_sym_app
 *)
val apply_eq_sym : eq_sym_app -> types
val dest_eq_sym : types -> eq_sym_app

(*
 * An application of eq_ind
 *)
type eq_ind_app =
  {
    at_type : types;
    p : types;
    trm1 : types;
    trm2 : types;
    h : types;
    b : types;
  }

(*
 * Convert between a term and an eq_app
 *)
val apply_eq_ind : eq_ind_app -> types
val dest_eq_ind : types -> eq_ind_app
                                
(*
 * An application of eq_refl
 *)
type eq_refl_app =
  {
    typ : types;
    trm : types;
  }

(*
 * Convert between a term and an eq_refl
 *)
val apply_eq_refl : eq_refl_app -> types
val dest_eq_refl : types -> eq_refl_app
                                
(*
 * An application of existT
 *)
type existT_app =
  {
    index_type : types;
    packer : types;
    index : types;
    unpacked : types;
  }

(*
 * Convert between a term and an existT_app
 *)
val pack_existT : existT_app -> types
val dest_existT : types -> existT_app

(*
 * An application of sigT
 *)
type sigT_app =
  {
    index_type : types;
    packer : types;
  }

(*
 * Convert between a term and a sigT_app
 *)
val pack_sigT : sigT_app -> types
val dest_sigT : types -> sigT_app

(*
 * Build the eta-expansion of a term known to have a sigma type.
 *)
val eta_sigT : constr -> types -> constr

(*
 * An application of sigT_rect
 *)
type sigT_elim =
  {
    to_elim : sigT_app;
    packed_type : types;
    unpacked : types;
    arg : types;
  }

(*
 * Convert between a term and a sigT_elim
 *)
val elim_sigT : sigT_elim -> types
val dest_sigT_elim : types -> sigT_elim

(*
 * Left projection of a sigma type given a sigma type and term of that type
 *)
val project_index : sigT_app -> types -> types

(*
 * Right projection of a sigma type given a sigma type and term of that type
 *)
val project_value : sigT_app -> types -> types

(*
 * Both projections in an (index, value) tuple
 *)
val projections : sigT_app -> types -> (types * types)

(* --- Inductive types and their eliminators --- *)

(*
 * Fail if the inductive type is mutually inductive or coinductive
 *)
val check_inductive_supported : mutual_inductive_body -> unit

(*
 * Determine if a term represents an inductive eliminator
 * For now, this is a naive syntactic check
 *)
val is_elim : env -> types -> bool

(*
 * Get the type of an inductive type
 *)
val type_of_inductive : env -> int -> mutual_inductive_body -> types

(*
 * Get an inductive type from an eliminator, if possible
 *)
val inductive_of_elim : env -> pconstant -> mutual_inductive option

(*
 * Lookup the eliminator over the type sort
 *)
val type_eliminator : env -> inductive -> types

(*
 * Applications of eliminators
 *)
type elim_app =
  {
    elim : types;
    pms : types list;
    p : types;
    cs : types list;
    final_args : types list;
  }

val apply_eliminator : elim_app -> types
val deconstruct_eliminator : env-> evar_map -> types -> elim_app

(*
 * Given the recursive type and the type of a case of an eliminator,
 * determine the number of inductive hypotheses
 *)
val num_ihs : env -> types -> types -> int

(* Determine whether template polymorphism is used for a one_inductive_body *)
val is_ind_body_template : one_inductive_body -> bool

(* Construct the arity of an inductive type from a one_inductive_body *)
val arity_of_ind_body : one_inductive_body -> types

(*
 * Create an Entries.local_entry from a Rel.Declaration.t
 *)
val make_ind_local_entry : CRD.t -> Id.t * Entries.local_entry

(*
 * Given a Declarations.abstract_inductive_universes, create an
 * Entries.inductive_universes and an instantiated universe
 * context Univ.UContext.t
 *)
val make_ind_univs_entry : abstract_inductive_universes -> Entries.inductive_universes * Univ.UContext.t

(*
 * For an inductive type in an environment, return the inductive's arity and
 * recursion-quantified constructor types, all consistently instantiated with fresh
 * universe levels, and return the universe-synchronized environment. If global
 * is true, the global environment is also synchronized with the new universe
 * levels and constraints. A descriptor for the inductive type's universe
 * properties is also returned.
 *)
val open_inductive : ?global:bool -> env -> Inductive.mind_specif -> env * Entries.inductive_universes * types * types list

(*
 * Declare a new inductive type in the global environment. Note that the arity
 * must quantify all parameters and that each constructor type must quantify
 * a recursive reference and then all parameters (i.e.,
 * forall (I : arity) (P : params), ...).
 *)
val declare_inductive : Id.t -> Id.t list -> bool -> Entries.inductive_universes -> int -> types -> types list -> inductive

(* --- Environments --- *)

(* Look up all indexes from a list in an environment *)
val lookup_rels : int list -> env -> Rel.Declaration.t list

(* Return a list of all indexes in an environment, starting with 1 *)
val all_rel_indexes : env -> int list

(* Return a list of all bindings in an environment, starting with the closest *)
val lookup_all_rels : env -> Rel.Declaration.t list

(* Push something to the highest position in an environment *)
val push_last : Rel.Declaration.t -> env -> env

(*
 * Return a list of relative indexes, from highest to lowest, of size n
 *)
val mk_n_rels : int -> types list

(*
 * Push to an environment
 *)
val push_local : (name * types) -> env -> env
val push_let_in : (name * types * types) -> env -> env

(* Is the rel declaration a local assumption? *)
val is_rel_assum : ('constr, 'types) Rel.Declaration.pt -> bool

(* Is the rel declaration a local definition? *)
val is_rel_defin : ('constr, 'types) Rel.Declaration.pt -> bool

(*
 * Construct a rel declaration
 *)
val rel_assum : Name.t * 'types -> ('constr, 'types) Rel.Declaration.pt
val rel_defin : Name.t * 'constr * 'types -> ('constr, 'types) Rel.Declaration.pt

(*
 * Project a component of a rel declaration
 *)
val rel_name : ('constr, 'types) Rel.Declaration.pt -> Name.t
val rel_value : ('constr, 'types) Rel.Declaration.pt -> 'constr option
val rel_type : ('constr, 'types) Rel.Declaration.pt -> 'types

(*
 * Map over a rel context with environment kept in synch
 *)
val map_rel_context : env -> (env -> Rel.Declaration.t -> 'a) -> Rel.t -> 'a list

(*
 * Bind all local declarations in the relative context onto the body term as
 * products, substituting away (i.e., zeta-reducing) any local definitions.
 *)
val smash_prod_assum : Rel.t -> types -> types

(*
 * Bind all local declarations in the relative context onto the body term as
 * lambdas, substituting away (i.e., zeta-reducing) any local definitions.
 *)
val smash_lam_assum : Rel.t -> constr -> constr

(*
 * Decompose the first n product bindings, zeta-reducing let bindings to reveal
 * further product bindings when necessary.
 *)
val decompose_prod_n_zeta : int -> types -> Rel.t * types

(*
 * Decompose the first n lambda bindings, zeta-reducing let bindings to reveal
 * further lambda bindings when necessary.
 *)
val decompose_lam_n_zeta : int -> constr -> Rel.t * constr

(* Is the named declaration an assumption? *)
val is_named_assum : ('constr, 'types) Named.Declaration.pt -> bool

(* Is the named declaration a definition? *)
val is_named_defin : ('constr, 'types) Named.Declaration.pt -> bool

(*
 * Construct a named declaration
 *)
val named_assum : Id.t * 'types -> ('constr, 'types) Named.Declaration.pt
val named_defin : Id.t * 'constr * 'types -> ('constr, 'types) Named.Declaration.pt

(*
 * Project a component of a named declaration
 *)
val named_ident : ('constr, 'types) Named.Declaration.pt -> Id.t
val named_value : ('constr, 'types) Named.Declaration.pt -> 'constr option
val named_type : ('constr, 'types) Named.Declaration.pt -> 'types

(*
 * Map over a named context with environment kept in synch
 *)
val map_named_context : env -> (env -> Named.Declaration.t -> 'a) -> Named.t -> 'a list

(*
 * Lookup from an environment
 *)
val lookup_pop : int -> env -> (env * CRD.t list)
val force_constant_body : constant_body -> constr
val lookup_definition : env -> types -> types
val unwrap_definition : env -> types -> types

(*
 * Get bindings to push to an environment
 *)
val bindings_for_inductive :
  env -> mutual_inductive_body -> one_inductive_body array -> CRD.t list
val bindings_for_fix : name array -> types array -> CRD.t list

(*
 * Offset between an environment and an index, or two environments, respectively
 *)
val new_rels : env -> int -> int
val new_rels2 : env -> env -> int

(*
 * Append two contexts (inner first, outer second), shifting internal indices.
 *
 * The input contexts are assumed to share the same environment, such that any
 * external indices inside the now-inner context must be shifted to pass over
 * the now-outer context.
 *)
val context_app : Rel.t -> Rel.t -> Rel.t

(*
 * Reconstruct local bindings around a term
 *)
val recompose_prod_assum : Rel.t -> types -> types
val recompose_lam_assum : Rel.t -> types -> types

(*
 * Instantiate an abstract universe context, the result of which should be
 * pushed on the current environment (with Environ.push_context) then used
 * to update the current evar_map (with Evd.update_sigma_env).
 *)
val inst_abs_univ_ctx : Univ.AUContext.t -> Univ.UContext.t

(* --- Basic questions about terms --- *)

(*
 * Get the arity of a function or function type
 *)
val arity : types -> int

(*
 * Check whether a term (second argument) applies a function (first argument)
 * Don't consider terms convertible to the function
 *
 * In the plural version, check for both the second and third terms
 *)
val applies : types -> types -> bool
val apply : types -> types -> types -> bool

(*
 * Check whether a term either is exactly a function or applies it
 *
 * In the plural version, check for both the second and the third terms
 *)
val is_or_applies : types  -> types -> bool
val are_or_apply : types -> types -> types -> bool

(* Is the first term equal to a "head" (application prefix) of the second?
 * The notion of term equality is syntactic, by default modulo alpha, casts,
 * application grouping, and universes. The result of this function is an
 * informative boolean: an optional array, with None meaning false and Some
 * meaning true and giving the trailing arguments.
 *
 * This function is similar to is_or_applies, except for term equality and the
 * informative boolean result.
 *)
val eq_constr_head : ?eq_constr:(constr -> constr -> bool) -> constr -> constr -> constr array option

(* --- Convertibility, reduction, and types --- *)

(*
 * Type-checking
 *
 * Current implementation may cause universe leaks, which will just cause
 * conservative failure of the plugin
 *)
val infer_type : env -> evar_map -> types -> types

(* Safely infer the WHNF type of a term, updating the evar map. *)
val e_infer_type : env -> evar_map ref -> constr -> constr

(* Safely infer the sort of a term, updating the evar map. *)
val e_infer_sort : env -> evar_map ref -> constr -> Sorts.family

(* Safely instantiate a global reference, updating the evar map. *)
val e_new_global : evar_map ref -> global_reference -> constr

(* Convertibility *)
val convertible : env -> evar_map -> types -> types -> bool

(*
 * Reduction
 *)
val reduce_term : env -> types -> types (* betaiotazeta *)
val delta : env -> types -> types (* delta *)
val reduce_nf : env -> types ->  types (* nf_all *)
val reduce_type : env -> evar_map -> types -> types (* betaiotazeta on types *)
val chain_reduce : (* sequencing *)
  (env -> types -> types) ->
  (env -> types -> types) ->
  env ->
  types ->
  types

(*
 * Apply a function on a type instead of on the term
 *)
val on_type : (types -> 'a) -> env -> evar_map -> types -> 'a

(* 
 * Checks whether the types of two terms are convertible
 *)
val types_convertible : env -> evar_map -> types -> types -> bool

(* --- Basic mapping --- *)

val map_rec_env_fix :
  (env -> 'a -> 'b) ->
  ('a -> 'a) ->
  env ->
  'a ->
  name array ->
  types array ->
  'b

val map_term_env :
  (env -> 'a -> types -> types) ->
  ('a -> 'a) ->
  env ->
  'a ->
  types ->
  types

val map_term :
  ('a -> types -> types) ->
  ('a -> 'a) ->
  'a ->
  types ->
  types

(* --- Names --- *)

(*
 * Add a string suffix to a name identifier
 *)
val with_suffix : Id.t -> string -> Id.t

(* Turn a name into an optional identifier *)
val ident_of_name : Name.t -> Id.t option

(* Turn an identifier into an external (i.e., surface-level) reference *)
val reference_of_ident : Id.t -> Libnames.reference

(* Turn a name into an optional external (i.e., surface-level) reference *)
val reference_of_name : Name.t -> Libnames.reference option

(* Convert an external reference into a qualid *)
val qualid_of_reference : Libnames.reference -> Libnames.qualid

(* Convert a term into a global reference with universes (or raise Not_found) *)
val pglobal_of_constr : constr -> global_reference Univ.puniverses

(* Convert a global reference with universes into a term *)
val constr_of_pglobal : global_reference Univ.puniverses -> constr

type global_substitution = global_reference Globmap.t

(* Substitute global references throughout a term *)
val subst_globals : global_substitution -> constr -> constr

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

(*
 * Declare a new inductive family under the given name with the transformed type
 * arity and constructor types from the given inductive definition. Names for
 * the constructors remain the same.
 *
 * NOTE: Global side effects.
 *)
val transform_inductive : Id.t -> constr_transformer -> Inductive.mind_specif -> inductive

(*
 * Declare a new module structure under the given name with the compositionally
 * transformed (i.e., forward-substituted) components from the given module
 * structure. Names for the components remain the same.
 *
 * The optional initialization function is called immediately after the module
 * structure begins, and its returned subsitution is applied to all other module
 * elements.
 *
 * NOTE: Does not support functors or nested modules.
 * NOTE: Global side effects.
 *)
val transform_module_structure : ?init:(unit -> global_substitution) -> Id.t -> constr_transformer -> module_body -> ModPath.t

(* --- Application and arguments --- *)

(*
 * Get a list of all arguments of a type unfolded at the head
 * Return empty if it's not an application
 *)
val unfold_args : types -> types list

(*
 * Get the very last argument of an application
 *)
val last_arg : types -> types

(*
 * Get the very first function of an application
 *)
val first_fun : types -> types

(*
 * Fully unfold arguments, then get the argument at a given position
 *)
val get_arg : int -> types -> types
