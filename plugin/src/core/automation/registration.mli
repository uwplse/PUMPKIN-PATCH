(* --- Type definitions for tactic registration --- *)

type tactic = unit Proofview.tactic

(* The domain of a tactic is described by a list of types, such that a matching
 * goal type must be constructed only with types given in this list.
 *
 * TODO: We should probably distinguish between tactics that tolerate/require
 *       introduction of all hypotheses and those that are sensitive to it.
 * TODO: We really need a more sophisticated pattern language that can express
 *       restrictions such as a list of an arbitrary type.
 *)
type pattern = Term.types list

(* TODO: This is currently dummy code. *)
val applicable : pattern -> Term.types -> bool

exception Register_collision
exception Tactic_failure

(* Register the tactic under the given name, raising Register_collision if the
 * name is already in use.
 *)
val register_tactic : string -> tactic -> pattern -> unit

(* Remove the named tactic from the registration table, if present. *)
val unregister_tactic : string -> unit

(* Find the tactic registered under the given name, raising Not_found if no
 * tactic is registered under that name.
 *)
val lookup_tactic : string -> tactic * pattern

(* Find all tactics that support the given type. *)
val applicable_tactics : Term.types -> tactic list

(* Evaluate a tactic to solve the given goal. *)
val eval_tactic : tactic -> Term.types -> Term.constr

(* Call a registered tactic to solve the given goal. *)
val call_tactic : string -> Term.types -> Term.constr
