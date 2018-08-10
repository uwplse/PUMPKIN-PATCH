(* --- Merging environments --- *)

open Constr
open Environ
open Assumptions
open Coqterms

type merged_closure = env * types list * types list

(*
 * Merge two environments,
 * assuming certain terms are equal and substituting those equal terms
 *)
val merge_environments : env -> env -> equal_assumptions -> env

(*
 * Merge two closures (environments and lists of terms),
 * assuming certain terms are equal and substituting those equal terms
 *)
val merge_closures : closure -> closure -> equal_assumptions -> merged_closure
