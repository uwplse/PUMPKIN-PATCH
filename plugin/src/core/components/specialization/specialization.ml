(* --- Specialization Component --- *)

(*
 * The default approach (specialize_using specialize_term)
 * is function application followed by betaiota reduction.
 *
 * We expose more advanced specialization approaches so that it is
 * easy to customize how this is called, which is useful
 * for future extension to the tool.
 *)

open Environ
open Term
open Coqterms
open Reducers

type specializer = env -> types -> types array -> types

(* --- Top-level --- *)

let specialize_using (s : specializer) env f args =
  s env f args

(* --- Conversion between specializers and reducers --- *)

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
     s env f_body args
  | _ ->
     failwith "Term should be of the form (fun args => f args)"

(* Convert a specializer into a reducer by taking arguments *)
let specialize_to (args : types array) (s : specializer) : reducer =
  fun env f -> s env f args

(*
 * Convert a specializer into a reducer by taking the function
 * This only handles a single argument
 *)
let specialize_in (f : types) (s : specializer) : reducer =
  fun env arg -> s env f (Array.make 1 arg)

(* Convert a reducer into a specializer in the obvious way *)
let reducer_to_specializer (r : reducer) : specializer =
  fun env f args -> r env (mkApp (f, args))

(* --- Defaults --- *)

(* Default specialization *)
let specialize_term : specializer =
  reducer_to_specializer reduce_term

(* --- Custom specializers --- *)

(* Specialize without reduction (so just apply) *)
let specialize_no_reduce : specializer =
  reducer_to_specializer do_not_reduce
