(* --- Type definitions for lemma registry --- *)

val register_lemma : string -> Term.constr -> unit

val unregister_lemma : string -> unit

val lookup_lemma : string -> Term.constr

val find_lemma : Environ.env -> Term.types -> Term.constr option
