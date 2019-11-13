open Envutils
open Substitution

(*
 * Refactoring functionality
 *)

(* Replace all subterms convertible with conv_trm in trm *)
let replace_all_convertible env conv_trm trm sigma =
  let trm = unwrap_definition env trm in
  all_conv_substs env sigma (conv_trm, conv_trm) trm

