(* Simple auxiliary functions for Coq terms *)

open Environ
open Evd
open Term
open Declarations
open Names
open Univ
open Command
open Collections

(* Auxiliary types *)

type closure = env * (types list)

(* --- Representations --- *)

let intern (env : env) (evm : evar_map) (t : Constrexpr.constr_expr) : types =
  let (trm, _) = Constrintern.interp_constr env evm t in
  trm

let extern (env : env) (evm : evar_map) (trm : types) : Constrexpr.constr_expr =
  Constrextern.extern_constr true env evm trm

(* --- Terms --- *)

(* Define a new Coq term *)
let define_term (n : Id.t) (env : env) (evm : evar_map) (trm : types) : unit =
  do_definition
    n
    (Global, false, Definition)
    None
    []
    None
    (extern env evm trm)
    None
    (Lemmas.mk_hook (fun _ _ -> ()))

(* The identity proposition *)
let id_prop : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Datatypes"; "Init"; "Coq"])))
       (Label.make "idProp"))

(* The identity type *)
let id_typ : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Datatypes"; "Init"; "Coq"])))
       (Label.make "id"))

(* Get the Coq identity term for typ *)
let identity_term (env : env) (typ : types) : types =
  let id = mkApp (id_prop, singleton_array typ) in
  try
    let _ = Typeops.infer env id in id
  with _ -> mkApp (id_typ, singleton_array typ)

(* Determine if a term applies an identity term *)
let applies_identity (trm : types) : bool =
  match kind_of_term trm with
  | App (f, _) ->
     eq_constr f id_prop || eq_constr f id_typ
  | _ ->
     false

(* eq_ind_r *)
let eq_ind_r : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_ind_r"))

(* eq_ind *)
let eq_ind : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_ind"))

(* eq_rec_r *)
let eq_rec_r : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_rec_r"))

(* eq_rec *)
let eq_rec : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_rec"))

(* eq_sym *)
let eq_sym : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_sym"))

(*
 * Check if a term is prop
 *)
let is_prop (trm : types) : bool =
  match kind_of_term trm with
  | Sort s ->
     s = prop_sort
  | _ ->
     false

(*
 * Check if a term is a rewrite via eq_ind or eq_ind_r
 * For efficiency, just check eq_constr
 * Don't consider convertible terms for now
 *)
let is_rewrite (trm : types) : bool =
  eq_constr trm eq_ind_r ||
  eq_constr trm eq_ind ||
  eq_constr trm eq_rec_r ||
  eq_constr trm eq_rec

(* Lookup a def in env *)
let lookup_definition (env : env) (def : types) : types =
  match kind_of_term def with
  | Const (c, u) ->
     let c_body = (lookup_constant c env).const_body in
     (match c_body with
      | Def cs -> Mod_subst.force_constr cs
      | OpaqueDef o -> Opaqueproof.force_proof (Global.opaque_tables ()) o
      | _ -> failwith "an axiom has no definition")
  | Ind _ -> def
  | _ ->  failwith "not a definition"

(* Fully lookup a def in env, but return the term if it is not a definition *)
let rec unwrap_definition (env : env) (trm : types) : types =
  try
    unwrap_definition env (lookup_definition env trm)
  with _ ->
    trm

(* Zoom all the way into a lambda term *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_rel (n, None, t) env) b
  | _ ->
     (env, trm)

(*
 * Reconstruct a lambda from an environment
 *)
let rec reconstruct_lambda (env : env) (b : types) : types =
  if nb_rel env = 0 then
    b
  else
    let (n, _, t) = lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda env' (mkLambda (n, t, b))

(*
 * Reconstruct a product from an environment
 *)
let rec reconstruct_prod (env : env) (b : types) : types =
  if nb_rel env = 0 then
    b
  else
    let (n, _, t) = lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_prod env' (mkProd (n, t, b))

(* --- Inductive types --- *)

(* Get the body of a mutually inductive type *)
let lookup_mutind_body (i : mutual_inductive) (env : env) : mutual_inductive_body =
  lookup_mind i env

(* Get the type of a mutually inductive type *)
let type_of_inductive (env : env) (mutind_body : mutual_inductive_body) (ind_body : one_inductive_body) : types =
  let univ_context = mutind_body.mind_universes in
  let univ_instance = UContext.instance univ_context in
  let mutind_spec = (mutind_body, ind_body) in
  Inductive.type_of_inductive env (mutind_spec, univ_instance)

(* Don't support mutually inductive or coinductive types yet (TODO) *)
let check_inductive_supported (mutind_body : mutual_inductive_body) : unit =
  let ind_bodies = mutind_body.mind_packets in
  if not (Array.length ind_bodies = 1) then
    failwith "mutually inductive types not yet supported"
  else
    if (mutind_body.mind_finite = Decl_kinds.CoFinite) then
      failwith "coinductive types not yet supported"
    else
      ()

(*
 * Check if a constant is an inductive elminator
 * If so, return the inductive type
 * Currently uses naming scheme, eventually should use structure
 * (Check how the "induction using" tactic detects this)
 *
 * TODO clean me after changes
 *)
let inductive_of_elim (env : env) (pc : pconstant) : mutual_inductive option =
  let (c, u) = pc in
  let kn = Constant.canonical c in
  let (modpath, dirpath, label) = KerName.repr kn in
  let rec try_find_ind is_rev =
    try
      let label_string = Label.to_string label in
      let label_length = String.length label_string in
      let split_index = String.rindex_from label_string (if is_rev then (label_length - 3) else label_length) '_'  in
      let suffix_length = label_length - split_index in
      let suffix = String.sub label_string split_index suffix_length in
      if (suffix = "_ind" || suffix = "_rect" || suffix = "_rec" || suffix = "_ind_r") then
        let ind_label_string = String.sub label_string 0 split_index in
        let ind_label = Label.of_id (Id.of_string_soft ind_label_string) in
        let ind_name = MutInd.make1 (KerName.make modpath dirpath ind_label) in
        lookup_mutind_body ind_name env;
        Some ind_name
      else
        if not is_rev then
          try_find_ind true
        else
          None
    with _ ->
      if not is_rev then
        try_find_ind true
      else
        None
  in try_find_ind false

(*
 * Get the number of constructors for an inductive type
 *
 * When we implement mutually inductive types, we may need to
 * update this heuristic.
 *)
let num_constrs (mutind_body : mutual_inductive_body) : int =
  Array.fold_left
    (fun n i ->
      n + (Array.length i.mind_consnames))
    0
    mutind_body.mind_packets

(* --- Convertibility of terms --- *)

(*
 * Check whether two terms are convertible, but ignore universe inconsistency
 * This is a workaround we should eventually fix
 * Though it doesn't seem to matter for patch-finding
 *)
let conv_ignoring_univ_inconsistency (env : env) (evm : evar_map) (trm1 : types) (trm2 : types) : bool =
  try
    Reductionops.is_conv env evm trm1 trm2
  with _ ->
    match (kind_of_term trm1, kind_of_term trm2) with
    | (Sort (Type u1), Sort (Type u2)) -> true
    | _ -> false

(* Checks whether two terms are convertible in env with the empty evar environment *)
let convertible (env : env) (trm1 : types) (trm2 : types) : bool =
  conv_ignoring_univ_inconsistency env empty trm1 trm2

(* Checks whether two terms are convertible in env with evars *)
let convertible_e (env : env) (evm : evar_map) (trm1 : types) (trm2 : types) : bool =
  conv_ignoring_univ_inconsistency env evm trm1 trm2

(*
 * Like concls_convertible, but expect exactly the same number of arguments
 * in the same order
 *)
let rec concls_convertible (env : env) (typ1 : types) (typ2 : types) : bool =
  match (kind_of_term typ1, kind_of_term typ2) with
  | (Prod (n1, t1, b1), Prod (n2, t2, b2)) ->
     if convertible env t1 t2 then
       concls_convertible (push_rel (n1, None, t1) env) b1 b2
     else
       false
  | _ ->
     convertible env typ1 typ2

(*
 * Check whether all terms in l1 and l2 are convertible in env
 *)
let all_convertible (env : env) (l1 : types list) (l2 : types list) : bool =
  List.for_all2 (convertible env) l1 l2

(*
 * Check if two arrays of arguments are all convertible with each other
 *)
let args_convertible (env : env) (a1 : types array) (a2 : types array) : bool =
  apply_to_arrays (all_convertible env) a1 a2

(* --- Types --- *)

(* Infer the type of trm in env, using the unsafe type judgment
 * The term we eventually produce is type-safe because real type-checking occurs later *)
let infer_type (env : env) (trm : types) : types =
  let jmt = Typeops.infer env trm in
  j_type jmt

(* Check whether a term has a given type *)
let has_type (env : env) (typ : types) (trm : types) : bool =
  try
    let trm_typ = infer_type env trm in
    convertible env trm_typ typ
  with _ -> false

(* --- Convertibility of types --- *)

(* Checks whether the types of two terms are convertible *)
let types_convertible (env : env) (trm1 : types) (trm2 : types) : bool =
  try
    let typ1 = infer_type env trm1 in
    let typ2 = infer_type env trm2 in
    convertible env typ1 typ2
  with _ -> false

(* --- Existential variables --- *)

(* Terms with existential variables *)
type eterm = evar_map * types
type eterms = evar_map * (types array)

(* --- Unification --- *)

(* Check whether a term is unifiable with a term of a given type *)
let unifiable (env : env) (typ : types) ((evm, trm) : eterm) : (evar_map option) =
  let (evm', typ_evar) = Evarutil.new_evar env evm typ in
  try
    Some (Evarconv.the_conv_x env trm typ_evar evm')
with _ -> None

(* --- Auxiliary functions for dealing with two terms at once --- *)

type kind = (types, types) kind_of_term
let kinds_of_terms = map_tuple kind_of_term

