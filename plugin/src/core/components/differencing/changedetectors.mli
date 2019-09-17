(* --- Change detectors --- *)

open Cutlemma
open Environ
open Constr
open Evd
open Stateutils
open Kindofchange

(*
 * Given a difference in proofs with goals and an optional lemma to cut by,
 * determine what has changed about the proof
 *)
val find_kind_of_change :
  cut_lemma option -> (* optional lemma to cut by *)
  env -> (* environment of old goal *)
  (constr * constr) -> (* old proof, new proof *)
  (types * types) -> (* old goal, new goal *)
  evar_map -> (* state *)
  kind_of_change state (* the kind of change, and updated state *)
