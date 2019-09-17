(* --- Merging environments --- *)

open Constr
open Environ
open Assumptions

(*
 * Merge two environments,
 * assuming certain terms are equal and substituting those equal terms
 *)
val merge_environments :
  (env * env) -> (* old and new environments *)
  equal_assumptions -> (* assumptions *)
  env (* common environment *)

(*
 * Merge two terms,
 * assuming certain terms are equal and substituting those equal terms
 *)
val merge_terms :
  (env * env) -> (* old and new envs *)
  (constr * constr) -> (* old and new terms *)
  equal_assumptions -> (* assumptions *)
  env * constr * constr (* common env, and updated old and new terms *)

(*
 * Merge two lists of terms,
 * assuming certain terms are equal and substituting those equal terms
 *)
val merge_term_lists :
  (env * env) -> (* old and new envs *)
  (constr list * constr list) -> (* old and new terms *)
  equal_assumptions -> (* assumptions *)
  env * constr list * constr list (* common env, and updated old and new terms *)
