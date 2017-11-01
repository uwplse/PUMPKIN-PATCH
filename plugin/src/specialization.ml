(* --- Specialization Component --- *)

open Term
open Environ
open Coqterms

type specializer = env -> types -> types array -> types
type reducer = env -> types -> types

(* --- Top-level --- *)

let specialize_using (s : specializer) env f args =
  s env f args

let reduce_using (r : reducer) env trm =
  r env trm

(* --- Specializers --- *)

(* Specialize f by args *)
let specialize_term (env : env) (f : types) (args : types array) : types =
  Reduction.nf_betaiota env (mkApp (f, args))

(* --- Reducers --- *)

(*
 * Specialize an applied function in a term body by its arguments.
 *
 * If the term does not have one of these forms:
 * 1) f args
 * 2) (fun ... => f args)
 * then this will fail.
 *
 * This will delta-reduce the function f if necessary.
 * At the bottom level, it returns betaiota reduction.
 *)
let rec specialize_body (s : specializer) (env : env) (t : types) : types =
  match kind_of_term t with
  | Lambda (n, t, b) ->
     mkLambda (n, t, specialize_body s (push_rel (n, None, t) env) b)
  | App (f, args) ->
     let f_body = unwrap_definition env f in
     specialize_using s env f_body args
  | _ ->
     failwith "Term should be of the form (fun args => f args)"

(*
 * Specialize the body of a term using the supplied reducer if
 * the predicate p is true on the body. If the term is a function,
 * then this recurses into the body and checks the condition, and so on.
 * It specializes as soon as the condition holds.
 *)
let rec reduce_body_if p (r : reducer) env trm =
  if p env trm then
    reduce_using r env trm
  else
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       reduce_body_if p r (push_rel (n, None, t) env) b
    | _ ->
       failwith "Could not specialize"

(* Convert a specializer into a reducer by taking arguments *)
let specialize_to (args : types array) (s : specializer) : reducer =
  fun env f -> s env f args

(*
 * Convert a specializer into a reducer by taking the function
 * This only handles a single argument
 *)
let specialize_in (f : types) (s : specializer) : reducer =
  fun env arg -> s env f (Array.make 1 arg)
