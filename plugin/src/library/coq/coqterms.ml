(* Simple auxiliary functions for Coq terms *)

open Util
open Collections
open Context
open Environ
open Constr
open Names
open Constrexpr
open Evd
open Utilities
open Declarations
open Decl_kinds
open Constrextern

module CRD = Context.Rel.Declaration

(* Auxiliary types *)

type closure = env * (types list)

(* --- Representations --- *)

let intern (env : env) (evm : evar_map) (t : Constrexpr.constr_expr) : types =
  let (trm, _) = Constrintern.interp_constr env evm t in
  EConstr.to_constr evm trm

let extern (env : env) (evm : evar_map) (trm : types) : Constrexpr.constr_expr =
  Constrextern.extern_constr true env evm (EConstr.of_constr trm)

(* Convert an external reference into a qualid *)
let qualid_of_reference r =
  CAst.with_val identity (Libnames.qualid_of_reference r)

(* --- Terms --- *)

(* https://github.com/ybertot/plugin_tutorials/blob/master/tuto1/src/simple_declare.ml *)
let edeclare ident (_, poly, _ as k) ~opaque sigma udecl body tyopt imps hook refresh =
  let open EConstr in
  (* XXX: "Standard" term construction combinators such as `mkApp`
     don't add any universe constraints that may be needed later for
     the kernel to check that the term is correct.

     We could manually call `Evd.add_universe_constraints`
     [high-level] or `Evd.add_constraints` [low-level]; however, that
     turns out to be a bit heavyweight.

     Instead, we call type inference on the manually-built term which
     will happily infer the constraint for us, even if that's way more
     costly in term of CPU cycles.

     Beware that `type_of` will perform full type inference including
     canonical structure resolution and what not.
   *)
  let env = Global.env () in
  let sigma =
    if refresh then
      fst (Typing.type_of ~refresh:false env sigma body)
    else
      sigma
  in
  let sigma = Evd.minimize_universes sigma in
  let body = to_constr sigma body in
  let tyopt = Option.map (to_constr sigma) tyopt in
  let uvars_fold uvars c =
    Univ.LSet.union uvars (Univops.universes_of_constr env c) in
  let uvars = List.fold_left uvars_fold Univ.LSet.empty
    (Option.List.cons tyopt [body]) in
  let sigma = Evd.restrict_universe_context sigma uvars in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let ubinders = Evd.universe_binders sigma in
  let ce = Declare.definition_entry ?types:tyopt ~univs body in
  DeclareDef.declare_definition ident k ce ubinders imps hook

(* Define a new Coq term *)
let define_term ?typ (n : Id.t) (evm : evar_map) (trm : types) (refresh : bool) =
  let k = (Global, Flags.is_universe_polymorphism(), Definition) in
  let udecl = Univdecls.default_univ_decl in
  let nohook = Lemmas.mk_hook (fun _ x -> x) in
  let etrm = EConstr.of_constr trm in
  let etyp = Option.map EConstr.of_constr typ in
  edeclare n k ~opaque:false evm udecl etrm etyp [] nohook refresh

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
  match kind trm with
  | App (f, _) ->
     equal f id_prop || equal f id_typ
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
  match kind trm with
  | Sort s ->
     s = Sorts.prop
  | _ ->
     false

(*
 * Check if a term is a rewrite via eq_ind or eq_ind_r
 * For efficiency, just check eq_constr
 * Don't consider convertible terms for now
 *)
let is_rewrite (trm : types) : bool =
  equal trm eq_ind_r ||
  equal trm eq_ind ||
  equal trm eq_rec_r ||
  equal trm eq_rec

(* Is the first term equal to a "head" (application prefix) of the second?
 * The notion of term equality is syntactic (i.e., no environment) and defaults
 * to syntactic equality modulo alpha, casts, grouping, and universes. The
 * result of this function is an informative boolean: an optional array, with
 * None meaning false and Some meaning true and giving the trailing arguments.
 *
 * This function is similar to is_or_applies, except for term equality and the
 * informative boolean result.
 *)
let eq_constr_head ?(eq_constr=eq_constr_nounivs) term term' =
  let head, args = decompose_app term in
  let head', args' = decompose_app term' in
  if eq_constr head head' && List.prefix_of eq_constr args args' then
    Some (List.skipn (List.length args) args' |> Array.of_list)
  else
    None

(* Lookup a def in env *)
let lookup_definition (env : env) (def : types) : types =
  match kind def with
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
  match kind trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_rel CRD.(LocalAssum(n, t)) env) b
  | _ ->
     (env, trm)

(*
 * Reconstruct a lambda from an environment
 *)
let rec reconstruct_lambda (env : env) (b : types) : types =
  if nb_rel env = 0 then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda env' (mkLambda (n, t, b))

(*
 * Reconstruct a product from an environment
 *)
let rec reconstruct_prod (env : env) (b : types) : types =
  if nb_rel env = 0 then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_prod env' (mkProd (n, t, b))

(* --- Inductive types --- *)

(* Get the body of a mutually inductive type *)
let lookup_mutind_body i (env : env) : mutual_inductive_body =
  lookup_mind i env

(* Get the type of a mutually inductive type *)
let type_of_inductive (env : env) (mutind_body : mutual_inductive_body) (ind_body : one_inductive_body) : types =
  let univs = Declareops.inductive_polymorphic_context mutind_body in
  let univ_instance = Univ.make_abstract_instance univs in
  let mutind_spec = (mutind_body, ind_body) in
  Inductive.type_of_inductive env (mutind_spec, univ_instance)

(* Don't support mutually inductive or coinductive types yet (TODO) *)
let check_inductive_supported (mutind_body : mutual_inductive_body) : unit =
  let ind_bodies = mutind_body.mind_packets in
  if not (Array.length ind_bodies = 1) then
    failwith "mutually inductive types not yet supported"
  else
    if (mutind_body.mind_finite = CoFinite) then
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
let inductive_of_elim (env : env) (pc : pconstant) =
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
        ignore (lookup_mutind_body ind_name env);
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
let conv_ignoring_univ_inconsistency env evm (trm1 : types) (trm2 : types) : bool =
  let etrm1 = EConstr.of_constr trm1 in
  let etrm2 = EConstr.of_constr trm2 in
  try
    Reductionops.is_conv env evm etrm1 etrm2
  with _ ->
    match map_tuple kind (trm1, trm2) with
    | (Sort (Sorts.Type u1), Sort (Sorts.Type u2)) -> true
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
  match (kind typ1, kind typ2) with
  | (Prod (n1, t1, b1), Prod (n2, t2, b2)) ->
     if convertible env t1 t2 then
       concls_convertible (push_rel CRD.(LocalAssum(n1, t1)) env) b1 b2
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

(*
 * Check whether the arguments to two applied functions are all convertible
 * in an environment.
 *
 * This fails with an error if the supplied terms are not applied functions.
 *)
let fun_args_convertible (env : env) (t1 : types) (t2 : types) : bool =
  if not (isApp t1 && isApp t2) then
    failwith "Need an application to check if arguments are convertible"
  else
    let (_, args1) = destApp t1 in
    let (_, args2) = destApp t2 in
    args_convertible env args1 args2
                     
(* --- Modules --- *)

(*
 * Pull any functor parameters off the module signature, returning the list of
 * functor parameters and the list of module elements (i.e., fields).
 *)
let decompose_module_signature mod_sign =
  let rec aux mod_arity mod_sign =
    match mod_sign with
    | MoreFunctor (mod_name, mod_type, mod_sign) ->
      aux ((mod_name, mod_type) :: mod_arity) mod_sign
    | NoFunctor mod_fields ->
      mod_arity, mod_fields
  in
  aux [] mod_sign

(*
 * Define an interactive (i.e., elementwise) module structure, with the
 * functional argument called to populate the module elements.
 *
 * The optional argument specifies functor parameters.
 *)
let declare_module_structure ?(params=[]) ident declare_elements =
  let mod_sign = Vernacexpr.Check [] in
  let mod_path =
    Declaremods.start_module Modintern.interp_module_ast None ident params mod_sign
  in
  Dumpglob.dump_moddef mod_path "mod";
  declare_elements ();
  let mod_path = Declaremods.end_module () in
  Dumpglob.dump_modref mod_path "mod";
  Flags.if_verbose Feedback.msg_info
    Pp.(str "\nModule " ++ Id.print ident ++ str " is defined");
  mod_path

(* Type-sensitive transformation of terms *)
type constr_transformer = env -> evar_map ref -> constr -> constr

let force_constant_body const_body =
  match const_body.const_body with
  | Def const_def ->
    Mod_subst.force_constr const_def
  | OpaqueDef opaq ->
    Opaqueproof.force_proof (Global.opaque_tables ()) opaq
  | _ ->
    CErrors.user_err ~hdr:"force_constant_body"
      (Pp.str "An axiom has no defining term")
                                                             
(*
 * Declare a new constant under the given name with the transformed term and
 * type from the given constant.
 *
 * NOTE: Global side effects.
 *)
let transform_constant ident tr_constr const_body =
  let env =
    match const_body.const_universes with
    | Monomorphic_const univs ->
      Global.env () |> Environ.push_context_set univs
    | Polymorphic_const univs ->
      CErrors.user_err ~hdr:"transform_constant"
        Pp.(str "Universe polymorphism is not supported")
  in
  let term = force_constant_body const_body in
  let evm = ref (Evd.from_env env) in
  let term' = tr_constr env evm term in
  let type' = tr_constr env evm const_body.const_type in
  define_term ~typ:type' ident !evm term' true |> Globnames.destConstRef
                                         
(*
 * Declare a new module structure under the given name with the compositionally
 * transformed (i.e., forward-substituted) components from the given module
 * structure. Names for the components remain the same.
 *
 * The optional initialization function is called immediately after the module
 * structure begins, and its returned subsitution is applied to all other module
 * elements.
 *
 * NOTE: Does not support functors or nested modules.
 * NOTE: Global side effects.
 *)
let transform_module_structure ?(init=const Globmap.empty) ident tr_constr mod_body =
  let mod_path = mod_body.mod_mp in
  let mod_arity, mod_elems = decompose_module_signature mod_body.mod_type in
  assert (List.is_empty mod_arity); (* Functors are not yet supported *)
  let transform_module_element subst (label, body) =
    let ident = Label.to_id label in
    let tr_constr env evm = subst_globals subst %> tr_constr env evm in
    match body with
    | SFBconst const_body ->
      let const = Constant.make2 mod_path label in
      if Globmap.mem (ConstRef const) subst then
        subst (* Do not transform schematic definitions. *)
      else
        let const' = transform_constant ident tr_constr const_body in
        Globmap.add (ConstRef const) (ConstRef const') subst
    | SFBmind mind_body ->
      check_inductive_supported mind_body;
      let ind = (MutInd.make2 mod_path label, 0) in
      let ind_body = mind_body.mind_packets.(0) in
      let ind' = transform_inductive ident tr_constr (mind_body, ind_body) in
      let ncons = Array.length ind_body.mind_consnames in
      let list_cons ind = List.init ncons (fun i -> ConstructRef (ind, i + 1)) in
      let sorts = ind_body.mind_kelim in
      let list_elim ind = List.map (Indrec.lookup_eliminator ind) sorts in
      Globmap.add (IndRef ind) (IndRef ind') subst |>
      List.fold_right2 Globmap.add (list_cons ind) (list_cons ind') |>
      List.fold_right2 Globmap.add (list_elim ind) (list_elim ind')
    | SFBmodule mod_body ->
      Feedback.msg_warning
        Pp.(str "Skipping nested module structure " ++ Label.print label);
      subst
    | SFBmodtype sig_body ->
      Feedback.msg_warning
        Pp.(str "Skipping nested module signature " ++ Label.print label);
      subst
  in
  declare_module_structure
    ident
    (fun () ->
       ignore (List.fold_left transform_module_element (init ()) mod_elems))


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

(* --- Auxiliary functions for dealing with two terms at once --- *)

let kinds_of_terms = map_tuple kind

