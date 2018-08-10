open Environ
open Collections
open Declarations
open Constr
open Coqterms
open Names

module CRD = Context.Rel.Declaration

type 'a contextual = env -> 'a

(* --- General environment management auxiliary functions --- *)

(* Look up all indexes from is in env *)
let lookup_rels (is : int list) (env : env) : CRD.t list =
 List.map (fun i -> lookup_rel i env) is

(* Return a list of all indexes in env, starting with 1 *)
let all_rel_indexes (env : env) : int list =
  from_one_to (nb_rel env)

(* Return a list of all bindings in env, starting with the closest *)
let lookup_all_rels (env : env) : CRD.t list =
  lookup_rels (all_rel_indexes env) env

(*
 * Push something to the highest position in an environment.
 *
 * Note: We need pop_rel_conext (nb_rel env) env rather than empty_env
 * because empty_env does not contain global definitions like nat.
 *)
let push_last (decl : CRD.t) (env : env) : env =
  List.fold_left
    (fun en decl -> push_rel decl en)
    (pop_rel_context (nb_rel env) env)
    (decl :: (List.rev (lookup_all_rels env)))

(* --- Getting bindings for terms --- *)

(*
 * Inductive types create bindings that we need to push to the environment
 * This function gets those bindings
 *)
let bindings_for_inductive (env : env) (mutind_body : mutual_inductive_body) (ind_bodies : one_inductive_body list) : CRD.t list =
  List.map
    (fun ind_body ->
      let name_id = ind_body.mind_typename in
      let typ = type_of_inductive env mutind_body ind_body in
      CRD.LocalAssum(Names.Name name_id, typ))
    ind_bodies

(*
 * A fixpoint creates bindings that we need to push to the environment
 * This function gets all of those bindings
 *)
let bindings_for_fix (names : Name.t array) (typs : types array) : CRD.t list =
  Array.to_list
    (CArray.map2_i
      (fun i name typ -> CRD.LocalAssum (name, Vars.lift i typ))
      names typs)
