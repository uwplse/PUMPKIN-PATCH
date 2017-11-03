(* Search configuration *)

open Term
open Environ
open Coqterms
open Proofcat
open Proofcatterms
open Collections
open Debruijn
open Utilities
open Proofdiff
open Reducers
open Assumptions

(* --- Auxiliary --- *)

let terms_convertible env_o env_n src_o src_n dst_o dst_n =
  convertible env_o src_o dst_o && convertible env_n src_n dst_n

let context_envs = map_tuple context_env
let context_terms = map_tuple context_term

(* --- Cutting by intermediate lemmas/guiding search --- *)

type cut_lemma =
  {
    lemma : types;
    app : types;
  }

let build_cut_lemma (env : env) (app : types) : cut_lemma =
  let (_, t, _) = destLambda app in
  let lemma = lookup_definition env t in
  { lemma; app; }

let get_lemma (cut : cut_lemma) =
  cut.lemma

let get_app (cut : cut_lemma) =
  cut.app

(* Test if a type is exactly the type of the lemma to cut by *)
let is_cut_strict env lemma typ =
  try
    concls_convertible env (reduce_term env lemma) (reduce_term env typ)
  with _ ->
    false

(* Test if a term has exactly the type of the lemma to cut by *)
let has_cut_type_strict env cut trm =
  try
    let typ = reduce_term env (infer_type env trm) in
    is_cut_strict env (get_lemma cut) typ
  with _ ->
    false

(* Flip the conclusions of a cut lemma *)
let rec flip_concls lemma =
  match kind_of_term lemma with
  | Prod (n, t, b) when isProd b ->
     mkProd (n, t, flip_concls b)
  | Prod (n, t, b) ->
     mkProd (n, unshift b, shift t)
  | _ ->
     failwith "Could not reverse the lemma conclusions"

(* Test if a term has exactly the type of the lemma to cut by in reverse *)
let has_cut_type_strict_rev env cut trm =
  try
    let typ = reduce_term env (infer_type env trm) in
    is_cut_strict env (flip_concls (get_lemma cut)) typ
  with _ ->
    false

(* Test if a term has the type of the lemma or its reverse *)
let has_cut_type_strict_sym env cut trm =
  has_cut_type_strict env cut trm || has_cut_type_strict_rev env cut trm

(* Check if a type is loosely the cut lemma (can have extra hypotheses) *)
let rec is_cut env lemma typ =
  match kinds_of_terms (lemma, typ) with
  | (Prod (nl, tl, bl), Prod (nt, tt, bt)) ->
     if not (isProd bl || isProd bt) then
       is_cut_strict env lemma typ
     else
       if convertible env tl tt then
         is_cut (push_rel (nl, None, tl) env) bl bt
       else
         let cut_l = is_cut (push_rel (nl, None, tl) env) bl (shift typ) in
         let cut_r = is_cut (push_rel (nt, None, tt) env) (shift lemma) bt in
         cut_l || cut_r
  | _  ->
     false

(* Check if a term has loosely the cut lemma type (can have extra hypotheses) *)
let has_cut_type env cut trm =
  try
    let typ = reduce_term env (infer_type env trm) in
    is_cut env (get_lemma cut) typ
  with _ ->
    false

(* Check if a term is loosely an application of the lemma to cut by *)
let has_cut_type_app env cut trm =
  try
    let typ = shift (reduce_term env (infer_type env trm)) in
    let env_cut = push_rel (Anonymous, None, get_lemma cut) env in
    let app = get_app cut in
    let app_app = reduce_term env_cut (mkApp (app, singleton_array (mkRel 1))) in
    let app_app_typ = infer_type env_cut app_app in
    is_cut env_cut app_app_typ typ
  with _ ->
    false

(* Filter a list of terms to those with the (loose) cut lemma type *)
let filter_cut env cut trms =
  List.filter (has_cut_type env cut) trms

(* Filter a list of terms to those that apply the (loose) cut lemma type *)
let filter_applies_cut env cut trms =
  List.filter (has_cut_type_app env cut) trms

(*
 * This returns true when the candidates we have patch the lemma we cut by
 *)
let are_cut env cut cs =
  List.length (filter_cut env cut cs) = List.length cs

(* --- Kinds of changes --- *)

(*
 * Represents the kind of change we are searching for, for now either:
 * 1) A change in conclusions, or
 * 2) A change in an inductive type we are doing induction over that preserves
 *    the shape of the inductive type
 * 3) A change in a fixpoint
 *    definition we are proving a property about inductively
 *    that preserves the shape of the definition
 * 4) A change in conclusions of a case of an inductive type that definitely
 *    cannot be factored out (or that the user does not want to factor out),
 *    as in sum-like inductive types like exists
 *)
type kind_of_change =
  | Conclusion
  | InductiveType of types * types
  | FixpointCase of (types * types) * cut_lemma
  | ConclusionCase of (cut_lemma option)

let is_conclusion c =
  c = Conclusion

let is_inductive_type c =
  match c with
  | InductiveType (_, _) -> true
  | _ -> false

let is_fixpoint_case c =
  match c with
  | FixpointCase ((_, _), _) -> true
  | _ -> false

let is_conclusion_case c =
  match c with
  | ConclusionCase _ -> true
  | _ -> false

(* --- Options --- *)

(*
 * Options for search:
 * 1) The is_ind boolean determines when we are in the inductive
 *    case of an inductive proof and have just encountered two different
 *    inductive hypotheses. Right now it is very primitive; we may need a better
 *    condition to determine this later. This matters for some heuristics,
 *    which may fire when we don't want them to fire.
 * 2) The change field holds the kind of change we are searching for.
 * 3) The same_h function determines when two types we induct over are
      "the same" for the sake of search.
 * 4) The update_goals function takes in the old goals and an updated
 *    difference in proofs and adds updated goals to the difference in proofs.
 * 5) The is_app function determines whether one proof may be a function
 *    of the other proof.
 *
 * TODO update comment with other field explanations
 *)
type options =
  {
    is_ind : bool;
    change : kind_of_change;
    same_h : types -> types -> bool;
    update_goals : goal_proof_diff -> proof_cat_diff -> goal_proof_diff;
    swap_goals : goal_term_diff -> goal_term_diff;
    reset_goals : goal_case_diff -> goal_case_diff;
    is_app : goal_proof_diff -> bool;
  }

let update_search_goals opts = opts.update_goals
let swap_search_goals opts = opts.swap_goals
let reset_case_goals opts = opts.reset_goals
let same_h opts = opts.same_h
let is_app opts = opts.is_app
let get_change opts = opts.change
let is_ind opts = opts.is_ind

let set_change opts change = { opts with change = change }
let set_is_ind opts is_ind = { opts with is_ind = is_ind }

(* --- Configuring options --- *)

(*
 * Given a kind of change, configure the same_h function:
 * 1) If we are searching for a difference in types we are inducting over,
 *    then two types we induct over are "the same" if they are either identical
 *    or are the same as the types we changed.
 * 2) If we are searching for a difference in conclusions or definitions, then
 *    two types we induct over are "the same" if they are identical.
 *
 * POST-DEADLINE: No need for goals here, just need environments
 *)
let configure_same_h change (d : lift_goal_diff) : types -> types -> bool =
  match change with
  | InductiveType (o, n) ->
     let goals = (old_proof d, new_proof d) in
     let (env_o, env_n) = context_envs goals in
     (fun f_o f_n ->
       let k_o = destConst f_o in
       let k_n = destConst f_n in
       let ind_o = mkInd (Option.get (inductive_of_elim env_o k_o), 0) in
       let ind_n = mkInd (Option.get (inductive_of_elim env_n k_n), 0) in
       (eq_constr f_o f_n) || (eq_constr ind_o o && eq_constr ind_n n))
  | _ ->
     eq_constr

(*
 * Given a set of goals, update the goal terms for a change in types.
 * Eliminate the terms we encounter from the goal.
 *)
 let update_goal_terms goals rel_o rel_n =
   let (g_o, g_n) = context_terms goals in
   let (env_o, env_n) = context_envs goals in
   let env_o' = push_rel rel_o env_o in
   let env_n' = push_rel rel_n env_n in
   let (_, _, t_o) = rel_o in
   let (_, _, t_n) = rel_n in
   let trim = terms_convertible env_o' env_n' t_o t_n in
   match kinds_of_terms (g_o, g_n) with
   | (Prod (_, t_g_o, b_o), Prod (_, t_g_n, b_n)) when trim t_g_o t_g_n ->
      (Term (b_o, env_o'), Term (b_n, env_n'))
   | _ ->
      (Term (shift g_o, env_o'), Term (shift g_n, env_n'))

(* Search for a difference in the changed constructor *)
let set_inductive_goals typ_o typ_n (d : 'a goal_diff) : 'a goal_diff =
  let (goal_o, proof_o) = old_proof d in
  let (goal_n, proof_n) = new_proof d in
  let assums = assumptions d in
  let env = context_env goal_o in
  let d_typs = difference typ_o typ_n no_assumptions in
  let d_constrs = ind_type_diff env d_typs in
  let (o, n) = (old_proof d_constrs, new_proof d_constrs) in
  let goal_o' = Context (Term (o, env), fid ()) in
  let goal_n' = Context (Term (n, env), fid ()) in
  difference (goal_o', proof_o) (goal_n', proof_n) assums

(*
 * Update the goals for a change in types
 *)
let update_goals_types d_old d =
  let (old_goal, _) = old_proof d_old in
  let (new_goal, _) = new_proof d_old in
  match kinds_of_terms (proof_terms d_old) with
  | (Lambda (n_o, t_o, _), Lambda (n_n, t_n, _)) ->
     let rel_o = (n_o, None, t_o) in
     let rel_n = (n_n, None, t_n) in
     let (g_o, g_n) = update_goal_terms (old_goal, new_goal) rel_o rel_n in
     let o = (Context (g_o, fid ()), old_proof d) in
     let n = (Context (g_n, fid ()), new_proof d) in
     difference o n (assumptions d)
  | _ ->
     let o = (old_goal, old_proof d) in
     let n = (new_goal, new_proof d) in
     difference o n (assumptions d)

(*
 * Given a change, determine how to update goals:
 * 1) If it's a change in types, then update the environments and
      eliminate variables we encounter.
 * 2) If it's a change in conclusions or definitions,
      then update the goals to the current conclusions.
 *)
let configure_update_goals change d_old d =
  match change with
  | InductiveType (typ_o, typ_n) ->
     update_goals_types d_old d
  | _ ->
     add_goals d

(*
 * Given a change, determine how to test whether a proof might apply
 * another proof:
 * 1) If it's a change in types, then check whether the new proof
 *    may apply the old proof.
 * 2) If it's a change in conclusions or definitions,
 *    then check whether the old proof may apply the new proof.
 *)
let configure_is_app change d =
  match (kinds_of_terms (proof_terms d), change) with
  | ((_, App (_, _)), InductiveType (_, _)) ->
     true
  | ((App (_, _), _), _) ->
     true
  | _ ->
     false

(*
 * Given a change, determine the goals for testing whether a proof
 * might apply to another proof:
 * 1) If it's a change in types, then swap the goals
 * 2) If it's a change in conclusions or definitions,
 *    then keep the goals as-is
 *)
let configure_swap_goals change d =
  match change with
  | InductiveType (_, _) ->
     swap_goals d
  | _ ->
     d

(*
 * Given options, determine how to reset the goals:
 *
 * 1) If it is a change in types, then search for a difference
 *    in the changed constructor.
 * 2) If it is a change in conclusions or definitions, then search for the
 *    the difference in conclusions.
 *
 * POST-DEADLINE:
 * This is for different inductive cases. It probably shouldn't
 * be separate from everything else, eventually need to refactor
 * all the goal-resetting functions into some format that makes sense.
 *)
let configure_reset_goals change (d : goal_case_diff) : goal_case_diff =
  match change with
  | InductiveType (typ_o, typ_n) ->
     set_inductive_goals typ_o typ_n d
  | _ ->
     d

(*
 * If we are searching for a change in conclusion, then
 * depending on whether the first different term is a constructor
 * or an induction principle, assume the type is positive or negative,
 * respectively, and search accordingly
 *
 * This is a heuristic and may sometimes be wrong, so we should
 * expose an option to users as well (TODO)
 *)
let configure_kind_of_conclusion cut (d : goal_proof_diff) : kind_of_change =
  let (trm_o, trm_n) = proof_terms d in
  let rec configure trm_o trm_n =
    match kinds_of_terms (trm_o, trm_n) with
    | (Lambda (_, _, b_o), _) ->
       configure b_o trm_n
    | (_, Lambda (_, _, b_n)) ->
       configure trm_o b_n
    | (App (f_o, _), App (f_n, _)) when isConstruct f_o && isConstruct f_n ->
       ConclusionCase cut
    | _ ->
       Conclusion
  in configure trm_o trm_n

(*
 * Configure the kind of change to search for (type difference detection).
 * Search for a difference in type only if the type is a product
 * that takes a non-convertible premise, and that premise is a different
 * inductive type with the same shape.
 *
 * Otherwise, if the new conclusion contains some constant function that has
 * changed from a constant function in the same place in the old conclusion,
 * but all of its arguments are the same, then search for a difference in
 * definitions.
 *
 * Otherwise, search for a change in conclusion.
 *)
let configure_kind_of_change (d : goal_proof_diff) (cut : cut_lemma option) : kind_of_change =
  let d_goals = erase_proofs d in
  let goals = goal_types d_goals in
  let env = context_env (old_proof d_goals) in
  let r = reduce_remove_identities env in
  let old_goal = r (fst goals) in
  let new_goal = r (snd goals) in
  let rec configure env typ_o typ_n =
    match kinds_of_terms (typ_o, typ_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if (not (convertible env t_o t_n)) then
         let change = InductiveType (t_o, t_n) in
         let d_typs = difference t_o t_n no_assumptions in
         if same_shape env d_typs then
           InductiveType (t_o, t_n)
         else
           Conclusion
       else
         configure (push_rel (n_o, None, t_o) env) b_o b_n
    | (App (f_o, args_o), App (f_n, args_n)) ->
       let args_o = Array.to_list args_o in
       let args_n = Array.to_list args_n in
       if (not (List.length args_o = List.length args_n)) then
         Conclusion
       else
         if isConst f_o && isConst f_n && (not (convertible env f_o f_n)) then
           if all_convertible env args_o args_n then
             if not (Option.has_some cut) then
               failwith "Must supply cut lemma for change in fixpoint"
             else
               FixpointCase ((f_o, f_n), Option.get cut)
           else
             Conclusion
         else
           let arg_confs = List.map2 (configure env) args_o args_n in
           if List.for_all is_conclusion arg_confs then
             Conclusion
           else
             List.find (fun change -> not (is_conclusion change)) arg_confs
    | _ ->
       Conclusion
  in
  let change = configure env old_goal new_goal in
  if is_conclusion change then
    configure_kind_of_conclusion cut d
  else
    change

(*
 * Build configuration options for the search based on the goal diff
 *)
let configure_search (d : goal_proof_diff) (cut : cut_lemma option) : options =
  let change = configure_kind_of_change d cut in
  {
    is_ind = false;
    change = change;
    same_h = configure_same_h change (erase_proofs d);
    update_goals = configure_update_goals change;
    swap_goals = configure_swap_goals change;
    reset_goals = configure_reset_goals change;
    is_app = configure_is_app change;
  }
