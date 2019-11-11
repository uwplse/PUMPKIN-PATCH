(* --- Type definitions for differencers --- *)

open Constr
open Proofdiff
open Candidates
open Proofcat
open Kindofchange
open Evd
open Stateutils
open Assumptions
open Environ

type ('a, 'b) differencer = 'a proof_diff -> evar_map -> 'b state

type 'a candidate_differencer = ('a, candidates) differencer
type proof_differencer =
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  candidates state

type proof_diff_predicate =
  equal_assumptions ->
  (env * env) ->
  (constr * constr) ->
  (types * types) ->
  evar_map ->
  bool state

type term_differencer = types candidate_differencer
type ind_proof_differencer = (proof_cat * int) candidate_differencer

type args_differencer_flat =
  equal_assumptions ->
  (constr list * constr list) ->
  evar_map ->
  candidates state
  
type args_differencer =
  equal_assumptions ->
  (constr list * constr list) ->
  evar_map ->
  (candidates list) state

type 'a change_detector = ('a, kind_of_change) differencer
type proof_change_detector = (context_object * proof_cat) change_detector

type 'a predicate_differencer = ('a, bool) differencer
