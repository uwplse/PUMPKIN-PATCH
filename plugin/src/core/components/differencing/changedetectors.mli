(* --- Change detectors --- *)

open Cutlemma
open Evd
open Differencers

(*
 * Given a difference in proofs with goals and an optional lemma to cut by,
 * determine what has changed about the proof
 *)
val find_kind_of_change : cut_lemma option -> proof_change_detector
