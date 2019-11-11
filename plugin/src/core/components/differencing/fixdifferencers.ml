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
open Convertibility
open Stateutils

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
let rec get_goal_fix env (o, n, assums) =
  if equal o n then
    ret give_up
  else
    let rec get_goal_reduced assums (o, n) =
      let reduce_hd t sigma = reduce_unfold_whd env sigma t in
      bind
        (map_tuple_state reduce_hd (o, n))
        (fun (red_old, red_new) ->
          match map_tuple kind (red_old, red_new) with
          | (App (f1, args1), App (f2, args2)) when equal f1 f2 ->
             let args_diff = map_tuple Array.to_list (args1, args2) in
             diff_map_flat get_goal_reduced assums args_diff
          | _ when not (equal red_old red_new) ->
             let g = mkProd (Names.Name.Anonymous, red_old, shift red_new) in
             bind (fun sigma -> reduce_unfold env sigma g) (fun l -> ret [l])
          | _ ->
             ret give_up)
    in
    match map_tuple kind (o, n) with
    | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) ->
       branch_state
         (fun (t1, t2) sigma -> convertible env sigma t1 t2)
         (fun (t1, t2) ->
           bind
             (get_goal_fix (push_local (n1, t1) env) (b1, b2, assums))
             (map_state (fun c -> ret (mkProd (n1, t1, c)))))
         (fun _ ->
           get_goal_reduced no_assumptions (o, n))
         (t1, t2)
    | _ ->
       get_goal_reduced no_assumptions (o, n)

(* Same as the above, but at the top-level for the fixpoint case *)
let rec diff_fix_case env (o, n, assums) =
  let diff_case (ct1, m1, bs1) (ct2, m2, bs2) =
    branch_state
      (fun (m1, m2) sigma -> convertible env sigma m1 m2)
      (fun (m1, m2) ->
        if Array.length bs1 = Array.length bs2 then
          let env_m = push_local (Names.Name.Anonymous, m1) env in
          let diff_bs = diff_map_flat (fun assums (o, n) -> get_goal_fix env_m (o, n, assums)) in
          bind
            (map_tuple_state
               (diff_bs assums)
               (map_tuple Array.to_list (bs1, bs2), map_tuple Array.to_list (bs2, bs1)))
            (fun (cs1, cs2) -> ret (unshift_all (List.append cs1 cs2)))
        else
          ret give_up)
      (fun _ -> ret give_up)
      (m1, m2)
  in
  match map_tuple kind (o, n) with
  | (Lambda (n1, t1, b1), Lambda (_, t2, b2)) ->
     branch_state
       (fun (t1, t2) sigma -> convertible env sigma t1 t2)
       (fun (t1, t2) ->
         diff_fix_case (push_local (n1, t1) env) (b1, b2, assums))
       (fun _ -> ret give_up)
       (t1, t2)
  | (Case (_, ct1, m1, bs1), Case (_, ct2, m2, bs2)) ->
     diff_case (ct1, m1, bs1) (ct2, m2, bs2)
  | _ ->
     ret give_up

(* --- Top-level --- *)

(*
 * Find the difference between the cases of two fixpoints
 *
 * This operates at the term level, since compilation currently
 * doesn't model fixpoints.
 *)
let diff_fix_cases env (o, n, assums) =
  let old_term = unwrap_definition env o in
  let new_term = unwrap_definition env n in
  match map_tuple kind (old_term, new_term) with
  | (Fix ((_, i), (nso, tso, dso)), Fix ((_, j), (_, tsn, dsn))) when i = j ->
     branch_state
       (fun (tso, tsn) ->
         forall2_state
           (fun t1 t2 sigma -> convertible env sigma t1 t2)
           (Array.to_list tso)
           (Array.to_list tsn))
       (fun _ ->
         let env_fix = push_rel_context (bindings_for_fix nso tso) env in
         bind
           (diff_map_flat (fun assums (o, n) -> diff_fix_case env_fix (o, n, assums)) assums (Array.to_list dso, Array.to_list dsn))
           (fun ds ->
             let fs = List.map (reconstruct_lambda env_fix) ds in
             let args = Array.make 1 new_term in
             let apps = List.map (fun f -> mkApp (f, args)) fs in
             bind
               (fun sigma -> reduce_all reduce_term env sigma apps)
               (fun red_apps -> ret (unique equal red_apps))))
       (fun _ _ ->
         failwith "Cannot infer goals for generalizing change in definition")
       (tso, tsn)
  | _ ->
     failwith "Not a fixpoint"
