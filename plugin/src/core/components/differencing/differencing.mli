(* --- Differencing Component --- *)

open Searchopts
open Differencers

(*
 * Given a configuration, return the appropriate top-level differencer
 *)
val get_differencer : proof_differencer configurable
