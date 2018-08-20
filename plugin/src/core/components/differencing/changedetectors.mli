(* --- Change detectors --- *)

open Cutlemma
open Differencers
open Constr
open Evd
open Environ

(*
 * Given a difference in proofs with goals and an optional lemma to cut by,
 * determine what has changed about the proof
 *)
val find_kind_of_change : cut_lemma option -> env -> evar_map -> types change_detector
