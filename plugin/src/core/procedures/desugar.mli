open Environ
open Constr

(*
 * Translate the given term into an equivalent, bisimulative (i.e., homomorpic
 * reduction behavior) version using eliminators instead of match or fix
 * expressions.
 *
 * Mutual recursion and co-recursion are not supported.
 *)
val desugar_constr : env -> Evd.evar_map ref -> constr -> constr (* Coqterms.constr_transformer *)
