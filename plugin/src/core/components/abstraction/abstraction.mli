(* --- Abstraction Component --- *)

open Abstracters
open Environ
open Term
open Coqterms
open Candidates
open Abstractionconfig

(*--- Abstraction ---*)

(*
 * Try to lift candidates with an ordered list of abstraction strategies
 * Return as soon as one is successful
 * If all fail, return the empty list
 *)
val abstract_with_strategies : abstraction_config -> types list
