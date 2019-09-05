(* --- Type definitions for differencers --- *)

open Constr
open Proofdiff
open Candidates
open Proofcat
open Kindofchange
open Evd
open Stateutils

type ('a, 'b) differencer = 'a proof_diff -> 'b (* TODO remove when done *)
type ('a, 'b) differencer_todo = 'a proof_diff -> evar_map -> 'b state

type 'a candidate_differencer = ('a, candidates) differencer_todo
type proof_differencer = (context_object * proof_cat) candidate_differencer
type term_differencer = types candidate_differencer
type ind_proof_differencer = (proof_cat * int) candidate_differencer

type arr_differencer = (types array) candidate_differencer
type 'a candidate_list_differencer = ('a, candidates list) differencer_todo
type arr_list_differencer = (types array) candidate_list_differencer

type 'a change_detector = ('a, kind_of_change) differencer_todo
type proof_change_detector = (context_object * proof_cat) change_detector

type 'a predicate_differencer = ('a, bool) differencer_todo
type proof_diff_predicate = (context_object * proof_cat) predicate_differencer
