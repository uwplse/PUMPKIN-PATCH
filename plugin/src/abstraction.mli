(* Strategies for abstracting concrete terms *)

open Term
open Environ

type abstracter

(* Fully abstract each term, substituting every convertible subterm *)
val syntactic_full_strategy : abstracter

(* Fully abstract each term, substituting every subterm w/ convertible types *)
val types_full_strategy : abstracter

(* All combinations of abstractions of convertible subterms *)
val syntactic_all_strategy : abstracter

(* A pattern-based full abstraction strategy for constructors *)
val pattern_full_strategy : abstracter

(*
 * Abstract the candidates by subtituting actual args with abstract args,
 * using an abstraction strategy to determine when to substitute.
 *)
val abstract_candidates :
 abstracter -> env -> types list -> types list -> types list -> types list

