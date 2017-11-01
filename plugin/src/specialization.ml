(* --- Specialization Component --- *)

(*
 * The default approach (specialize_using specialize_term)
 * is function application followed by betaiota reduction.
 *
 * We expose more advanced specialization approaches so that it is
 * easy to customize how this is called, which is useful
 * for future extension to the tool.
 *)

open Environ
open Term
open Hofs
open Coqterms
open Utilities
open Debruijn

type specializer = env -> types -> types array -> types
type reducer = env -> types -> types

(* --- Top-level --- *)

let specialize_using (s : specializer) env f args =
  s env f args

let reduce_using (r : reducer) env trm =
  r env trm

let reduce_all (r : reducer) env (trms : types list) : types list =
  List.map (r env) trms

(* --- Combinators and converters --- *)

let chain_reduce (r1 : reducer) (r2 : reducer) env trm : types =
  r2 env (r1 env trm)

let try_reduce (r : reducer) (env : env) (trm : types) : types =
  try r env trm with _ -> trm

(*
 * Specialize an applied function in a term body by its arguments.
 *
 * If the term does not have one of these forms:
 * 1) f args
 * 2) (fun ... => f args)
 * then this will fail.
 *
 * This will delta-reduce the function f if necessary.
 * At the bottom level, it returns betaiota reduction.
 *)
let rec specialize_body (s : specializer) (env : env) (t : types) : types =
  match kind_of_term t with
  | Lambda (n, t, b) ->
     mkLambda (n, t, specialize_body s (push_rel (n, None, t) env) b)
  | App (f, args) ->
     let f_body = unwrap_definition env f in
     s env f_body args
  | _ ->
     failwith "Term should be of the form (fun args => f args)"

(*
 * Specialize the body of a term using the supplied reducer if
 * the predicate p is true on the body. If the term is a function,
 * then this recurses into the body and checks the condition, and so on.
 * It specializes as soon as the condition holds.
 *)
let rec reduce_body_if p (r : reducer) env trm =
  if p env trm then
    r env trm
  else
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       reduce_body_if p r (push_rel (n, None, t) env) b
    | _ ->
       failwith "Could not specialize"

(* Convert a specializer into a reducer by taking arguments *)
let specialize_to (args : types array) (s : specializer) : reducer =
  fun env f -> s env f args

(*
 * Convert a specializer into a reducer by taking the function
 * This only handles a single argument
 *)
let specialize_in (f : types) (s : specializer) : reducer =
  fun env arg -> s env f (Array.make 1 arg)

(* Convert a reducer into a specializer in the obvious way *)
let reducer_to_specializer (r : reducer) : specializer =
  fun env f args -> r env (mkApp (f, args))

(* --- Defaults --- *)

(* Default reducer *)
let reduce_term (env : env) (trm : types) : types =
  Reduction.nf_betaiota env trm

(* Default specialization *)
let specialize_term : specializer =
  reducer_to_specializer reduce_term

(* --- Custom reducers --- *)

(* Don't reduce *)
let do_not_reduce (env : env) (trm : types) : types =
  trm

(* Remove all applications of the identity function *)
let remove_identities (env : env) (trm : types) : types =
  map_term_if
    (fun _ t -> applies_identity t)
    (fun _ t ->
      match kind_of_term t with
      | App (_, args) ->
         Array.get args 1
      | _ ->
         t)
    id
    ()
    trm

(* Remove all applications of the identity function, then default reduce *)
let reduce_remove_identities : reducer =
  chain_reduce remove_identities reduce_term

(* Reduce and also unfold definitions *)
let reduce_unfold (env : env) (trm : types) : types =
  Reductionops.nf_betadeltaiota env Evd.empty trm

(* Reduce and also unfold definitions, but weak head *)
let reduce_unfold_whd (env : env) (trm : types) : types =
  Reductionops.whd_betadeltaiota env Evd.empty trm

(* Weak-head reduce a term if it is a let-in *)
let reduce_whd_if_let_in (env : env) (trm : types) : types  =
  if isLetIn trm then
    Reduction.whd_betaiotazeta env trm
  else
    trm

(*
 * This function removes any terms from the hypothesis of a lambda
 * that are not referenced in the body, so that the term
 * has only hypotheses that are referenced.
 *
 * This is a workaround for the way that the procedure for
 * changes in constructor arguments works.
 * Basically, it should return earlier once it finds the
 * goal patch. But right now, the implementation isn't great,
 * so instead we treat it like any other goal patch and add
 * more hypotheses to our patch, and then later we remove them.
 * We should fix this eventually.
 *)
let rec remove_unused_hypos (env : env) (trm : types) : types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     let env_b = push_rel (n, None, t) env in
     let b' = remove_unused_hypos env_b b in
     (try
        let num_rels = nb_rel env in
        let env_ill = push_rel (n, None, mkRel (num_rels + 1)) env in
        let _ = infer_type env_ill b' in
        remove_unused_hypos env (unshift b')
      with _ ->
        mkLambda (n, t, b'))
  | _ ->
     trm

(* --- Custom specializers --- *)

(* Specialize without reduction (so just apply) *)
let specialize_no_reduce : specializer =
  reducer_to_specializer do_not_reduce
