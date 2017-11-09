open Environ
open Collections
open Declarations
open Term
open Coqterms
open Names

(* --- General environment management auxiliary functions --- *)

(* Look up all indexes from is in env *)
let lookup_rels (is : int list) (env : env) : Context.rel_declaration list =
 List.map (fun i -> lookup_rel i env) is

(* Return a list of all indexes in env, starting with 1 *)
let all_rel_indexes (env : env) : int list =
  from_one_to (nb_rel env)

(* Return a list of all bindings in env, starting with the closest *)
let lookup_all_rels (env : env) : Context.rel_declaration list =
  lookup_rels (all_rel_indexes env) env

(*
 * Push something to the highest position in an environment.
 * 
 * Note: We need pop_rel_conext (nb_rel env) env rather than empty_env
 * because empty_env does not contain global definitions like nat.
 *)
let push_last ((n, b, t) : Context.rel_declaration) (env : env) : env =
  List.fold_left
    (fun en (na, bo, ty) -> push_rel (na, bo, ty) en)
    (pop_rel_context (nb_rel env) env)
    ((n, b, t) :: (List.rev (lookup_all_rels env)))

(* --- Getting bindings for terms --- *)

(*
 * Inductive types create bindings that we need to push to the environment
 * This function gets those bindings
 *)
let bindings_for_inductive (env : env) (mutind_body : mutual_inductive_body) (ind_bodies : one_inductive_body list) : Context.rel_declaration list =
  List.map
    (fun ind_body ->
      let name_id = ind_body.mind_typename in
      let typ = type_of_inductive env mutind_body ind_body in
      (Names.Name name_id, None, typ))
    ind_bodies

(*
 * A fixpoint creates bindings that we need to push to the environment
 * This function gets all of those bindings
 *)
let bindings_for_fix (names : name array) (typs : types array) : Context.rel_declaration list =
  Array.to_list
    (CArray.map2_i
      (fun i name typ -> (name, None, Vars.lift i typ))
      names typs)
