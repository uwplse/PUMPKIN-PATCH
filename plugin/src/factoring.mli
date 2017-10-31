(* --- The Factoring Component --- *)

open Term
open Environ

(*
 * Factors are a list of environment-type pairs, where the environment
 * contains all necessary assumptions. This is essentially a way
 * to avoid DeBruijn problems while reasoning about factors with hypotheses
 * that depend on earlier hypotheses; we can think of all of these
 * factors as functions living within a common environment as well.
 *)
type factors = (env * types) list

(*
 * Given a term, if the term is a function with type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F)
 *)
val factor_term : env -> types -> factors

(*
 * Apply factors to reconstruct a single term
 *)
val apply_factors : factors -> types
