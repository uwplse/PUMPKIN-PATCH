(* Substitution auxiliary functions *)

open Environ
open Constr
open Coqterms
open Hofs
open Debruijn

(* TODO clean up so retrieval is easier *)
type ('a, 'b) substitution = env -> 'a -> types -> 'b
type 'a comb_substitution = ('a, types list) substitution
type 'a type_substitution = ('a, types) substitution

(* Map a substitution over a term *)
let all_substs p env (src, dst) trm : types =
  map_term_env_if
    (fun en (s, _) t -> p en s t)
    (fun _ (_, d) _ -> d)
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm

(* Map all combinations of a substitution over a term *)
let all_substs_combs p env (src, dst) trm : types list =
  map_subterms_env_if
    (fun en (s, _) t -> p en s t)
    (fun _ (_, d) t -> [d; t])
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm

(* In env, substitute all subterms of trm that are convertible to src with dst *)
let all_conv_substs : (types * types) type_substitution =
  all_substs convertible

(* In env, substitute all subterms of trm that have a convertible type to the type of src with dst *)
let all_typ_substs : (types * types) type_substitution =
  all_substs types_convertible

(*
 * Check if a subterm matches applies a constructor function pat to
 * an argument with the type of itself
 *)
let constructs_recursively env c trm : bool =
  if isApp trm then
    try
      let (f, args) = destApp trm in
      let conv = convertible env in
      let types_conv = types_convertible env in
      conv f c && List.exists (types_conv trm) (Array.to_list args)
    with _ ->
      false
  else
    false

(*
 * Map a constructor substitution over a term
 * The constructor is a function c
 * This finds the outermost applications of c to an argument
 * with the type of the term itself, "undoing" the constructor
 * It substitutes in the first argument with that type
 *
 * Can generalize this further
 *)
let all_constr_substs env c trm : types =
  map_term_env_if
    constructs_recursively
    (fun _ _ t ->
      let (_, args_t) = destApp t in
      List.find (types_convertible env t) (Array.to_list args_t))
    shift
    env
    c
    trm

(* In env, return all substitutions of subterms of trm that are convertible to src with dst *)
let all_conv_substs_combs : (types * types) comb_substitution =
  all_substs_combs convertible

(* In env, return all substitutions of subterms of trm that have a convertible type to the type of src with dst *)
let all_typ_substs_combs : (types * types) comb_substitution =
  all_substs_combs types_convertible
