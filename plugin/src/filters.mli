(* Filters for terms and eterms *)

open Term
open Environ
open Coqterms

type 'a filter_strategy = env -> types -> 'a list -> 'a list

(* Filter a list of terms to those that have the goal type *)
val filter_by_type : types filter_strategy

(* Find the singleton list with the first term that has the goal type *)
val find_by_type : types filter_strategy

(* Filter a list of eterms to those unifiable with a term of the goal type *)
val filter_unifiable : eterm filter_strategy

(* Filter a list of terms to those not exactly the same as the supplied term *)
val filter_not_same : types filter_strategy

(* Filter a list of reduced candidates to those that do not reference the IH *)
val filter_ihs : env -> types list -> types list

