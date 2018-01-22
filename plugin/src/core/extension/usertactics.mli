(* --- Type definitions for tactic registry --- *)

type tactic = unit Proofview.tactic

exception Tactic_failure

val register_tactic : string -> tactic -> Term.types list -> unit

val unregister_tactic : string -> unit

val lookup_tactic : string -> tactic * Term.types list

(* Find all tactics that support the given type. *)
val find_tactics : Environ.env -> Term.types -> tactic list

(* Evaluate a tactic to solve the given goal. *)
val eval_tactic : Environ.env -> Evd.evar_map -> Term.types -> tactic -> Term.constr

(* Call a registered tactic to solve the given goal. *)
val call_tactic : Environ.env -> Evd.evar_map -> Term.types -> string -> Term.constr

(* Try all applicable tactics to solve the goal *)
val try_tactics : Environ.env -> Evd.evar_map -> Term.types -> Term.constr option
