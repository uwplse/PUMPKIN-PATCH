(* Basic types for proof search *)

open Term

type candidates = types list

(*
 * Candidates when we fail to find a patch
 *)
val give_up : candidates
