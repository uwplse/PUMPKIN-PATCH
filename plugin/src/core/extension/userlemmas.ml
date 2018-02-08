open Term
open Coqterms

(* TODO: Is a more subtle check for lemma compatibility needed?
 * TODO: Is caching lemma types worth the potential trouble with
 *       environment management?
 *)

(* TODO: Should save inferred type... *)
let registry : constr Registry.registry = Registry.create ()

let register_lemma key pf =
  Registry.register registry key pf

let unregister_lemma = Registry.unregister registry

let lookup_lemma = Registry.lookup registry

(* Find a lemma for a patch type, if one is registered. *)
let find_lemma env typ : constr option =
  let typ = Reducers.reduce_term env typ in
  match Registry.filter registry (has_type env typ) with
  | pf :: _ -> Some pf
  | [] -> None
