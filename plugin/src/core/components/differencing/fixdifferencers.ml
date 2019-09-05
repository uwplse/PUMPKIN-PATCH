(* --- Differencing of Fixpoints --- *)

open Utilities
open Constr
open Environ
open Proofdiff
open Candidates
open Reducers
open Assumptions
open Debruijn
open Higherdifferencers
open Evd
open Zooming
open Contextutils
open Envutils

(* --- TODO for backwards compatibility during refactor, fix w/ evar_map updates --- *)

let convertible env sigma t1 t2 = snd (Convertibility.convertible env sigma t1 t2)
let types_convertible env sigma t1 t2 = snd (Convertibility.types_convertible env sigma t1 t2)

(* --- End TODO --- *)

(* --- Cases --- *)

(*
 * Gets the change in the case of a fixpoint branch.
 * These are the goals for abstraction.
 * Since semantic differencing doesn't have a good model of fixpoints yet,
 * this is a little complicated, and currently works directly over
 * the old representation. It's also the only function so far
 * to delta-reduce, which we can learn from.
 *
 * But basically this detects a change in a fixpoint case and
 * just is super preliminary.
 * After the prototype we should model fixpoints better.
 *)
let rec get_goal_fix env evd (d : types proof_diff) : candidates =
  let old_term = old_proof d in
  let new_term = new_proof d in
  let assums = assumptions d in
  if equal old_term new_term then
    give_up
  else
    match map_tuple kind (old_term, new_term) with
    | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) when convertible env evd t1 t2 ->
       List.map
         (fun c -> mkProd (n1, t1, c))
         (get_goal_fix (push_rel CRD.(LocalAssum(n1, t1)) env) evd (difference b1 b2 assums))
    | _ ->
       let reduce_hd = reduce_unfold_whd env evd in
       let rec get_goal_reduced d : candidates =
         let _, red_old = reduce_hd (old_proof d) in
         let _, red_new = reduce_hd (new_proof d) in
         match map_tuple kind (red_old, red_new) with
         | (App (f1, args1), App (f2, args2)) when equal f1 f2 ->
            let d_args = difference args1 args2 no_assumptions in
            snd (diff_map_flat (fun t sigma -> sigma, get_goal_reduced t) d_args Evd.empty)
         | _ when not (equal red_old red_new) ->
            [snd (reduce_unfold env evd (mkProd (Names.Name.Anonymous, red_old, shift red_new)))]
         | _ ->
            give_up
       in get_goal_reduced (difference old_term new_term no_assumptions)

(* Same as the above, but at the top-level for the fixpoint case *)
let rec diff_fix_case env evd (d : types proof_diff) : candidates =
  let old_term = old_proof d in
  let new_term = new_proof d in
  let assums = assumptions d in
  let conv = convertible env evd in
  match map_tuple kind (old_term, new_term) with
  | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) when conv t1 t2 ->
     diff_fix_case (push_rel CRD.(LocalAssum(n1, t1)) env) evd (difference b1 b2 assums)
  | (Case (_, ct1, m1, bs1), Case (_, ct2, m2, bs2)) when conv m1 m2  ->
     if Array.length bs1 = Array.length bs2 then
       let env_m = push_rel CRD.(LocalAssum(Names.Name.Anonymous, m1)) env in
       let diff_bs l = snd (diff_map_flat (fun t sigma -> sigma, get_goal_fix env_m evd t) l evd) in
       List.map
         unshift
         (List.append
            (diff_bs (difference bs1 bs2 assums))
            (diff_bs (difference bs2 bs1 assums)))
     else
       give_up
  | _ ->
     give_up

(* --- Top-level --- *)

(*
 * Find the difference between the cases of two fixpoints
 *
 * This operates at the term level, since compilation currently
 * doesn't model fixpoints.
 *)
let diff_fix_cases env (d : types proof_diff) evd : candidates Stateutils.state =
  let old_term = unwrap_definition env (old_proof d) in
  let new_term = unwrap_definition env (new_proof d) in
  let assums = assumptions d in
  match map_tuple kind (old_term, new_term) with
  | (Fix ((_, i), (nso, tso, dso)), Fix ((_, j), (_, tsn, dsn))) when i = j ->
    if List.for_all2 (convertible env evd) (Array.to_list tso) (Array.to_list tsn) then
      let env_fix = push_rel_context (bindings_for_fix nso tso) env in
      let d_ds = difference dso dsn assums in
      let ds = snd (diff_map_flat (fun t sigma -> sigma, diff_fix_case env_fix evd t) d_ds evd) in
      let lambdas = List.map (reconstruct_lambda env_fix) ds in
      let apps =
        List.map
          (fun t -> mkApp (t, Array.make 1 new_term))
          lambdas
      in evd, unique equal (snd (reduce_all reduce_term env evd apps))
    else
      failwith "Cannot infer goals for generalizing change in definition"
  | _ ->
     failwith "Not a fixpoint"
