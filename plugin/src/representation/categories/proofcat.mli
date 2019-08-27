open Constr
open Environ
open Assumptions
open Evd
open Stateutils

(* Proof categories, core logic *)
(* Will go away soon *)

(* --- Type definitions --- *)

(* Types of objects and arrows *)
type type_context = Term of types * env | Gamma
type context_object = Context of type_context * int
type extension = AnonymousBinding | InductiveHypothesis of int | Index of int | LazyBinding of types * env | AppBinding of extension * extension

(* Initial context *)
val initial_context : context_object

(* Categories *)
type proof_cat
type arrow = context_object * extension * context_object

(* Initial category *)
val initial_category : evar_map -> proof_cat state

(* Initial and terminal objects *)
type initial_object = context_object option
type terminal_object = context_object option

(* --- Printing --- *)

(* Get an object as a string *)
val context_as_string : context_object -> string

(* Get an extension as a string *)
val extension_as_string : extension -> string

(* Get a proof category as a string *)
val proof_as_string : proof_cat -> evar_map -> string

(* --- Objects, extensions, and arrows --- *)

(*
 * Get the objects of a proof category
 *)
val objects : proof_cat -> evar_map -> (context_object list) state

(*
 * Get the arrows of a proof category
 *)
val morphisms : proof_cat -> arrow list

(*
 * True iff two objects are equal
 *)
val objects_equal : context_object -> context_object -> evar_map -> bool state

(*
 * True iff two objects are not equal
 *)
val objects_not_equal : context_object -> context_object -> evar_map -> bool state

(*
 * True iff the list of objects contains the object
 *)
val contains_object : context_object -> context_object list -> evar_map -> bool state

(*
 * True iff the list of objects doesn't contain the object
 *)
val not_contains_object : context_object -> context_object list -> evar_map -> bool state

(*
 * True iff two extensions are equal
 *)
val extensions_equal : extension -> extension -> evar_map -> bool state

(*
 * True iff two extensions are not equal
 *)
val extensions_not_equal : extension -> extension -> evar_map -> bool state

(*
 * True iff two extensions are equal with a set of assumptions
 *)
val extensions_equal_assums : equal_assumptions -> extension -> extension -> evar_map -> bool state

(*
 * True iff two arrows are equal
 *)
val arrows_equal : arrow -> arrow -> evar_map -> bool state

(*
 * True iff two arrows are not equal
 *)
val arrows_not_equal : arrow -> arrow -> evar_map -> bool state

(*
 * True iff the list of arrows contains the arrow
 *)
val contains_arrow : arrow -> arrow list -> evar_map -> bool state

(*
 * True iff the list of arrows doesn't contain the arrow
 *)
val not_contains_arrow : arrow -> arrow list -> evar_map -> bool state

(*
 * Map a function on the source of an arrow
 *)
val map_source : (context_object -> 'a) -> arrow -> 'a

(*
 * Map a function on the destination of an arrow
 *)
val map_dest : (context_object -> 'a) -> arrow -> 'a

(*
 * Map a function on the extension of an arrow
 *)
val map_ext : (extension -> 'a) -> arrow -> 'a

(*
 * Map a function on the destination of an arrow and return a new arrow
 *)
val map_source_arrow : (context_object -> context_object) -> arrow -> arrow

(*
 * Map a function on the source of an arrow and return a new arrow
 *)
val map_dest_arrow : (context_object -> context_object) -> arrow -> arrow

(*
 * Map a function on the extension of an arrow and return a new arrow
 *)
val map_ext_arrow : (extension -> extension) -> arrow -> arrow

(*
 * True iff an arrow maps from the provided object
 *)
val maps_from : context_object -> arrow -> evar_map -> bool state

(*
 * True iff an arrow maps to the provided object
 *)
val maps_to : context_object -> arrow -> evar_map -> bool state

(*
 * Return all objects from which an arrow flows
 *)
val hypotheses : arrow list -> context_object list

(*
 * Return all objects to which an arrow flows
 *)
val conclusions : arrow list -> context_object list

(*
 * Return all objects in a list except for the ones that equal a given object
 *)
val all_objects_except : context_object -> context_object list -> evar_map -> (context_object list) state

(*
 * Return all arrows in a list except for the ones that equal a given arrow
 *)
val all_arrows_except : arrow -> arrow list -> evar_map -> (arrow list) state

(*
 * Return all objects in a list except for the ones in another list
 *)
val all_objects_except_those_in : context_object list -> context_object list -> evar_map -> (context_object list) state

(*
 * Return all arrows in a list except for the ones in another list
 *)
val all_arrows_except_those_in : arrow list -> arrow list -> evar_map -> (arrow list) state

(*
 * Return all arrows from a list that start from a source object
 *)
val arrows_with_source : context_object -> arrow list -> evar_map -> (arrow list) state

(*
 * Return all arrows from a list that end with a destination object
 *)
val arrows_with_dest : context_object -> arrow list -> evar_map -> (arrow list) state

(*
 * Combine two lists of objects into a single list without duplicates
 *)
val combine_objects : context_object list -> context_object list -> evar_map -> (context_object list) state

(*
 * Combine two lists of arrows into a single list without duplicates
 *)
val combine_arrows : arrow list -> arrow list -> evar_map -> (arrow list) state

(*
 * Get all of the objects found in a list of arrows
 *)
val objects_of_arrows : arrow list -> evar_map -> (context_object list) state

(* --- Categories --- *)

(*
 * Make a proof category
 *)
val make_category :
  context_object list ->
  arrow list ->
  initial_object ->
  terminal_object ->
  evar_map ->
  proof_cat state

(*
 * Add an object to a category
 *)
val add_object : context_object -> proof_cat -> evar_map -> proof_cat state

(*
 * Remove an object from a category
 *)
val remove_object : context_object -> proof_cat -> evar_map -> proof_cat state

(*
 * Add an arrow to a category
 *)
val add_arrow : arrow -> proof_cat -> evar_map -> proof_cat state

(*
 * Check if a category has an initial object
 *)
val has_initial : proof_cat -> bool

(*
 * Check if a category has a terminal object
 *)
val has_terminal : proof_cat -> bool

(*
 * Check whether an object is initial in the category
 *)
val is_initial : proof_cat -> context_object -> evar_map -> bool state

(*
 * Check whether an object is terminal in the category
 *)
val is_terminal : proof_cat -> context_object -> evar_map -> bool state

(*
 * Set the initial object of a category
 *)
val set_initial : initial_object -> proof_cat -> evar_map -> proof_cat state

(*
 * Set the terminal object of a category
 *)
val set_terminal : terminal_object -> proof_cat -> evar_map -> proof_cat state

(*
 * Set the initial and terminal objects of a category
 *)
val set_initial_terminal : initial_object -> terminal_object -> proof_cat -> evar_map -> proof_cat state

(*
 * Get the initial object of a category, if it exists
 *)
val initial_opt : proof_cat -> initial_object

(*
 * Get the terminal object of a category, if it exists
 *)
val terminal_opt : proof_cat -> terminal_object

(*
 * Get the initial object of a category, and fail if it doesn't exist
 *)
val initial : proof_cat -> context_object

(*
 * Get the terminal object of a category, and fail if it doesn't exist
 *)
val terminal : proof_cat -> context_object

(*
 * Combine two proof categories, setting the initial and terminal objects
 *)
val combine : initial_object -> terminal_object -> proof_cat -> proof_cat -> evar_map -> proof_cat state

(* Check if a category contains an arrow *)
val category_contains_arrow : arrow -> proof_cat -> evar_map -> bool state

(*
 * Get the only arrow in a category
 * Fail if it has no arrows
 * Fail if it has more than one arrow
 *)
val only_arrow : proof_cat -> arrow

(* Determine if an object is a hypothesis in a proof category *)
val is_hypothesis : proof_cat -> context_object -> evar_map -> bool state

(* Determine if an object is not a hypothesis in a proof category *)
val is_not_hypothesis : proof_cat -> context_object -> evar_map -> bool state

(* Apply a function to the list of objects of c *)
val map_objects : (context_object list -> evar_map -> 'a state) -> proof_cat -> evar_map -> 'a state

(* Apply a function to the list of arrows of c *)
val map_arrows : (arrow list -> 'a) -> proof_cat -> 'a

(* --- Paths of explicit (not transitive or identity) arrows --- *)

(*
 * Get a list of explicit arrows on some path from an object in a category
 * If this path is a list, then this maintains order
 * Assumes there are no cycles
 *)
val arrows_from : proof_cat -> context_object -> evar_map -> (arrow list) state

(*
 * Get a list of explicit arrows on some path between two objects in a category
 * If this path is a list, then this maintains order
 * Assumes there are no cycles
 *)
val arrows_between : proof_cat -> context_object -> context_object -> evar_map -> (arrow list) state

(*
 * Find ordered paths from an object via explicit arrows
 *)
val paths_from : proof_cat -> context_object -> evar_map -> (arrow list list) state

(*
 * Get the length of the shortest path from the initial object to an object
 * If the object is the initial object, this is 0
 * Error if no initial object
 * Error if the object is unreachable
 *)
val shortest_path_length : proof_cat -> context_object -> evar_map -> int state

(* --- Functors --- *)

(*
 * Apply a functor over proof categories
 *)
val apply_functor :
  (context_object -> evar_map -> context_object state) ->
  (arrow -> arrow) ->
  proof_cat ->
  evar_map ->
  proof_cat state
