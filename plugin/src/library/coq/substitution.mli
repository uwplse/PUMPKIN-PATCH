(* Substitution auxiliary functions *)

open Environ
open Constr

(* TODO clean up so retrieval is easier *)
type ('a, 'b) substitution = env -> 'a -> types -> 'b
type 'a comb_substitution = ('a, types list) substitution
type 'a type_substitution = ('a, types) substitution

(*
 * In an environment, substitute all subterms of a term that are
 * convertible to a source term with a destination term.
 *
 * This checks convertibility before recursing, and so will replace at
 * the highest level possible.
 *)
val all_conv_substs : (types * types) type_substitution

(*
 * In an environment, substitute all subterms of a term that have
 * a convertible type to the type of a source term with a
 * destination term.
 *
 * This checks convertibility before recursing, and so will replace at
 * the highest level possible.
 *)
val all_typ_substs : (types * types) type_substitution

(*
 * In an environment, substitute all subterms of a term that apply a
 * constructor with the first argument with the same type as the constructor.
 * This effectively "undoes" the constructor.
 *
 * It's currently not smart enough to understand what to do when the
 * constructor has multiple arguments of the same type as the type itself,
 * like in tree-like inductive types. It's always going to try the left
 * case in a tree for now.
 *
 * This checks convertibility before recursing, and so will replace at
 * the highest level possible.
 *)
val all_constr_substs : types type_substitution

(*
 * In an environment, return all combinations of substitutions of
 * subterms of a term that are convertible with a source term
 * with a destination term.
 *)
val all_conv_substs_combs : (types * types) comb_substitution

(*
 * In an environment, return all combinations of substitutions of
 * subterms of a term that have a type that is convertible with
 * the type of a source term  with a destination term.
 *)
val all_typ_substs_combs : (types * types) comb_substitution
