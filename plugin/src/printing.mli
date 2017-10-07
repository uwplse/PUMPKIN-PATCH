(* Auxiliary functions for printing *)

open Format
open Names
open Term
open Environ

(* --- Strings --- *)

(* Using a supplied pretty printing function, prints directly to a string *)
val print_to_string : (formatter -> 'a -> unit) -> 'a -> string

(* --- Coq terms --- *)

(* Gets a name as a string *)
val name_as_string : name -> string

(* Gets a term as a string in an environment *)
val term_as_string : env -> types -> string

(* --- Coq environments --- *)

(* Gets an environment as a string *)
val env_as_string : env -> string

(* --- Debugging --- *)

(* Print a separator string *)
val print_separator : unit -> unit

(* Debug a term with a descriptor string *)
val debug_term : env -> types -> string -> unit

(* Debug a list of terms with a descriptor string *)
val debug_terms : env -> types list -> string -> unit

(* Debug an environment with a descriptor string *)
val debug_env : env -> string -> unit
