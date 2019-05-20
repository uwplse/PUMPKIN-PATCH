(*
 * Coq term and environment management
 *)

open Util
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

module Globmap = Globnames.Refmap
module Globset = Globnames.Refset

module CRD = Context.Rel.Declaration

(*
 * TODO remove unused functions for now
 *)

(* --- Auxiliary types --- *)
               
type closure = env * (types list)
               
(* --- Constants --- *)

let coq_init_specif =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["Specif"; "Init"; "Coq"]))

let coq_init_logic =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"]))

let coq_init_datatypes =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["Datatypes"; "Init"; "Coq"]))

(* sigma types *)
let sigT : types =
  mkInd (MutInd.make1 (KerName.make2 coq_init_specif (Label.make "sigT")), 0)

(* Introduction for sigma types *)
let existT : types =
  mkConstruct (fst (destInd sigT), 1)

(* Elimination for sigma types *)
let sigT_rect : types =
  mkConst (Constant.make2 coq_init_specif (Label.make "sigT_rect"))

(* Left projection *)
let projT1 : types =
  mkConst (Constant.make2 coq_init_specif (Label.make "projT1"))

(* Right projection *)
let projT2 : types =
  mkConst (Constant.make2 coq_init_specif (Label.make "projT2"))

(* equality *)
let eq : types =
  mkInd (MutInd.make1 (KerName.make2 coq_init_logic (Label.make "eq")), 0)

(* Constructor for quality *)
let eq_refl : types =
  mkConstruct (fst (destInd eq), 1)

(* Eliminator for quality *)
let eq_ind : types =
  mkConst (Constant.make2 coq_init_logic (Label.make "eq_ind"))

(* Symmetry *)
let eq_sym : types =
  mkConst (Constant.make2 coq_init_logic (Label.make "eq_sym"))

(* The identity proposition *)
let id_prop : types =
  mkConst (Constant.make2 coq_init_datatypes (Label.make "idProp"))

(* The identity type *)
let id_typ : types =
  mkConst (Constant.make2 coq_init_datatypes (Label.make "id"))

(* --- Questions about constants --- *)

(* Determine if a term applies an identity term *)
let applies_identity (trm : types) : bool =
  match kind trm with
  | App (f, _) ->
     equal f id_prop || equal f id_typ
  | _ ->
     false

(* --- Representations --- *)

(** Construct the external expression for a definition. *)
let expr_of_global (g : global_reference) : constr_expr =
  let r = extern_reference Id.Set.empty g in
  CAst.make @@ (CAppExpl ((None, r, None), []))

(* Intern a term (for now, ignore the resulting evar_map) *)
let intern env evd t : types =
  let (trm, _) = Constrintern.interp_constr env evd t in
  EConstr.to_constr evd trm

(* Extern a term *)
let extern env evd t : constr_expr =
  Constrextern.extern_constr true env evd (EConstr.of_constr t)

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

(* Safely extract the body of a constant, instantiating any universe variables. *)
let open_constant env const =
  let (Some (term, auctx)) = Global.body_of_constant const in
  let uctx = Universes.fresh_instance_from_context auctx |> Univ.UContext.make in
  let term = Vars.subst_instance_constr (Univ.UContext.instance uctx) term in
  let env = Environ.push_context uctx env in
  env, term

(* --- Application and arguments --- *)

(* Get a list of all arguments, fully unfolded at the head *)
let unfold_args_app trm =
  let (f, args) = destApp trm in
  let rec unfold trm =
    match kind trm with
    | App (f, args) ->
       List.append (unfold f) (Array.to_list args)
    | _ ->
       [trm]
  in List.append (List.tl (unfold f)) (Array.to_list args)

(* Like unfold_args_app, but return empty if it's not an application *)
let unfold_args trm =
  if isApp trm then unfold_args_app trm else []

(* Get the last argument of an application *)
let last_arg trm =
  if isApp trm then last (unfold_args trm) else failwith "not an application"

(* Get the first function of an application *)
let rec first_fun t =
  match kind t with
  | App (f, args) ->
     first_fun f
  | _ ->
     t

(*
 * Get the argument to an application of a property at argument position i
 * This unfolds all arguments first
 *)
let get_arg i trm =
  match kind trm with
  | App (_, _) ->
     let args = Array.of_list (unfold_args trm) in
     Array.get args i
  | _ ->
     failwith "not an application"

(* --- Constructing terms --- *)

(* mkApp with a list *)
let mkAppl (f, args) = mkApp (f, Array.of_list args)

(* Define a constant from an ID in the current path *)
let make_constant id =
  mkConst (Constant.make1 (Lib.make_kn id))

(* Recursively turn a product into a function *)
let rec prod_to_lambda trm =
  match kind trm with
  | Prod (n, t, b) ->
     mkLambda (n, t, prod_to_lambda b)
  | _ ->
     trm

(* Recursively turn a function into a product *)
let rec lambda_to_prod trm =
  match kind trm with
  | Lambda (n, t, b) ->
     mkProd (n, t, lambda_to_prod b)
  | _ ->
     trm

(*
 * An application of eq
 *)
type eq_app =
  {
    at_type : types;
    trm1 : types;
    trm2 : types;
  }

(*
 * Make an eq type
 *)
let apply_eq (app : eq_app) : types =
  mkAppl (eq, [app.at_type; app.trm1; app.trm2])

(*
 * Deconstruct an eq type
 *)
let dest_eq (trm : types) : eq_app =
  let [at_type; trm1; trm2] = unfold_args trm in
  { at_type; trm1; trm2 }

(*
 * An application of eq_sym
 *)
type eq_sym_app =
  {
    eq_typ : eq_app;
    eq_proof : types;
  }

(*
 * Make an eq type
 *)
let apply_eq_sym (app : eq_sym_app) : types =
  let eq_typ = app.eq_typ in
  mkAppl (eq_sym, [eq_typ.at_type; eq_typ.trm1; eq_typ.trm2; app.eq_proof])

(*
 * Deconstruct an eq type
 *)
let dest_eq_sym (trm : types) : eq_sym_app =
  let [at_type; trm1; trm2; eq_proof] = unfold_args trm in
  let eq_typ = { at_type; trm1; trm2 } in
  { eq_typ; eq_proof }
    
(*
 * An application of eq_ind
 *)
type eq_ind_app =
  {
    at_type : types;
    p : types;
    trm1 : types;
    trm2 : types;
    h : types;
    b : types;
  }

(*
 * Apply an eq_ind
 *)
let apply_eq_ind (app : eq_ind_app) : types =
  mkAppl (eq_ind, [app.at_type; app.trm1; app.p; app.b; app.trm2; app.h])

(* 
 * Deconstruct an eq_ind
 *)
let dest_eq_ind (trm : types) : eq_ind_app =
  let [at_type; trm1; p; b; trm2; h] = unfold_args trm in
  { at_type; trm1; p; b; trm2; h }

(*
 * An application of eq_refl
 *)
type eq_refl_app =
  {
    typ : types;
    trm : types;
  }

(*
 * Apply an eq_refl
 *)
let apply_eq_refl (app : eq_refl_app) : types =
  mkAppl (eq_refl, [app.typ; app.trm])

(* 
 * Deconstruct an eq_refl
 *)
let dest_eq_refl (trm : types) : eq_refl_app =
  let [typ; trm] = unfold_args trm in
  { typ; trm }

(*
 * An application of existT
 *)
type existT_app =
  {
    index_type : types;
    packer : types;
    index : types;
    unpacked : types;
  }

(*
 * Pack an existT term from an index type, packer, index, and unpacked version
 *)
let pack_existT (app : existT_app) : types =
  mkAppl (existT, [app.index_type; app.packer; app.index; app.unpacked])

(*
 * Deconstruct an existT term
 *)
let dest_existT (trm : types) : existT_app =
  let [index_type; packer; index; unpacked] = unfold_args trm in
  { index_type; packer; index; unpacked }

(*
 * An application of sigT
 *)
type sigT_app =
  {
    index_type : types;
    packer : types;
  }

(*
 * Pack a sigT type from an index type and a packer
 *)
let pack_sigT (app : sigT_app) =
  mkAppl (sigT, [app.index_type; app.packer])

(*
 * Deconsruct a sigT type from a type
 *)
let dest_sigT (typ : types) =
  let [index_type; packer] = unfold_args typ in
  { index_type; packer }

(*
 * Build the eta-expansion of a term known to have a sigma type.
 *)
let eta_sigT (term : constr) (typ : types) =
  let { index_type; packer } = dest_sigT typ in
  let fst = mkApp (projT1, [|index_type; packer; term|]) in
  let snd = mkApp (projT2, [|index_type; packer; term|]) in
  mkApp (existT, [|index_type; packer; fst; snd|])

(*
 * An application of sigT_rect
 *)
type sigT_elim =
  {
    to_elim : sigT_app;
    packed_type : types;
    unpacked : types;
    arg : types;
  }

(*
 * Eliminate a sigT given an index type, packer, packed type, unpacked term,
 * and the term itself
 *)
let elim_sigT (app : sigT_elim) =
  let index_type = app.to_elim.index_type in
  let packer = app.to_elim.packer in
  let packed_type = app.packed_type in
  let unpacked = app.unpacked in
  let arg = app.arg in
  mkAppl (sigT_rect, [index_type; packer; packed_type; unpacked; arg])

(*
 * Deconstruct an application of sigT_rect
 *)
let dest_sigT_elim (trm : types) =
  let [index_type; packer; packed_type; unpacked; arg] = unfold_args trm in
  let to_elim = { index_type ; packer } in
  { to_elim; packed_type; unpacked; arg }

(*
 * Left projection of a sigma type
 *)
let project_index (app : sigT_app) trm =
  mkAppl (projT1, [app.index_type; app.packer; trm])

(*
 * Right projection of a sigma type
 *)
let project_value (app : sigT_app) trm =
  mkAppl (projT2, [app.index_type; app.packer; trm])

(*
 * Both projections of a sigma type
 *)
let projections (app : sigT_app) trm =
  (project_index app trm, project_value app trm)

(* --- Convertibility, reduction, and types --- *)

(* Infer the type of trm in env *)
let infer_type (env : env) (evd : evar_map) (trm : types) : types =
  EConstr.to_constr evd (Typing.unsafe_type_of env evd (EConstr.of_constr trm))
                    
(* Safely infer the WHNF type of a term, updating the evar map *)
let e_infer_type env evm term =
  EConstr.of_constr term |> Typing.e_type_of ~refresh:true env evm |>
  Reductionops.whd_all env !evm |> EConstr.to_constr !evm

(* Safely infer the sort of a type, updating the evar map *)
let e_infer_sort env evm term =
  EConstr.of_constr term |> Typing.e_sort_of env evm |> Sorts.family

(* Safely instantiate a global reference, with proper universe handling *)
let e_new_global evm gref =
  Evarutil.e_new_global evm gref |> EConstr.to_constr !evm

(* Check whether two terms are convertible, ignoring universe inconsistency *)
let conv_ignoring_univ_inconsistency env evm (trm1 : types) (trm2 : types) : bool =
  let etrm1 = EConstr.of_constr trm1 in
  let etrm2 = EConstr.of_constr trm2 in
  try
    Reductionops.is_conv env evm etrm1 etrm2
  with _ ->
    match map_tuple kind (trm1, trm2) with
    | (Sort (Type u1), Sort (Type u2)) -> true
    | _ -> false

(* Checks whether two terms are convertible in env with no evars *)
let convertible (env : env) (evd : evar_map) (trm1 : types) (trm2 : types) : bool =
  conv_ignoring_univ_inconsistency env evd trm1 trm2

(*
 * Checks whether the conclusions of two dependent types are convertible,
 * modulo the assumption that every argument we encounter is equal when
 * the types of those arguments are convertible. Expect exactly the same
 * number of arguments in the same order.
 *)
let rec concls_convertible (env : env) (evd : evar_map) (typ1 : types) (typ2 : types) : bool =
  match (kind typ1, kind typ2) with
  | (Prod (n1, t1, b1), Prod (n2, t2, b2)) ->
     if convertible env evd t1 t2 then
       concls_convertible (push_rel CRD.(LocalAssum(n1, t1)) env) evd b1 b2
     else
       false
  | _ ->
     convertible env evd typ1 typ2
                                   
(* Check whether a term has a given type *)
let has_type (env : env) (evd : evar_map) (typ : types) (trm : types) : bool =
  try
    let trm_typ = infer_type env evd trm in
    convertible env evd trm_typ typ
  with _ -> false

(* Default reducer *)
let reduce_term (env : env) (trm : types) : types =
  EConstr.to_constr
    Evd.empty
    (Reductionops.nf_betaiotazeta env Evd.empty (EConstr.of_constr trm))

(* Delta reduction *)
let delta (env : env) (trm : types) =
  EConstr.to_constr
    Evd.empty
    (Reductionops.whd_delta env Evd.empty (EConstr.of_constr trm))

(*
 * There's a part of the env that has opacity info,
 * so if you want to make some things opaque, can add them
 * get env, store it, call set_strategy w/ opaque,
 * then revert later
 *
 * See environ.mli
 * set_oracle
 * set_strategy
 *)

(* nf_all *)
let reduce_nf (env : env) (trm : types) : types =
  EConstr.to_constr
    Evd.empty
    (Reductionops.nf_all env Evd.empty (EConstr.of_constr trm))

(* Reduce the type *)
let reduce_type (env : env) evd (trm : types) : types =
  reduce_term env (infer_type env evd trm)

(* Chain reduction *)
let chain_reduce rg rf (env : env) (trm : types) : types =
  rg env (rf env trm)

(* Apply on types instead of on terms *)
let on_type f env evd trm =
  f (reduce_type env evd trm)

(* Checks whether the types of two terms are convertible *)
let types_convertible (env : env) (evd : evar_map) (trm1 : types) (trm2 : types) : bool =
  try
    let typ1 = infer_type env evd trm1 in
    let typ2 = infer_type env evd trm2 in
    convertible env evd typ1 typ2
  with _ -> false

(* --- Environments --- *)

(* Look up all indexes from is in env *)
let lookup_rels (is : int list) (env : env) : CRD.t list =
 List.map (fun i -> lookup_rel i env) is

(* Return a list of all indexes in env, starting with 1 *)
let all_rel_indexes (env : env) : int list =
  from_one_to (nb_rel env)

(* Return a list of all bindings in env, starting with the closest *)
let lookup_all_rels (env : env) : CRD.t list =
  lookup_rels (all_rel_indexes env) env

(*
 * Push something to the highest position in an environment.
 *
 * Note: We need pop_rel_conext (nb_rel env) env rather than empty_env
 * because empty_env does not contain global definitions like nat.
 *)
let push_last (decl : CRD.t) (env : env) : env =
  List.fold_left
    (fun en decl -> push_rel decl en)
    (pop_rel_context (nb_rel env) env)
    (decl :: (List.rev (lookup_all_rels env)))

(* Make n relative indices, from highest to lowest *)
let mk_n_rels n =
  List.map mkRel (List.rev (from_one_to n))

(* Push a local binding to an environment *)
let push_local (n, t) = push_rel CRD.(LocalAssum (n, t))

(* Push a let-in definition to an environment *)
let push_let_in (n, e, t) = push_rel CRD.(LocalDef(n, e, t))

(* Is the rel declaration a local assumption? *)
let is_rel_assum = Rel.Declaration.is_local_assum

(* Is the rel declaration a local definition? *)
let is_rel_defin = Rel.Declaration.is_local_def

(* Make the rel declaration for a local assumption *)
let rel_assum (name, typ) =
  Rel.Declaration.LocalAssum (name, typ)

(* Make the rel declaration for a local definition *)
let rel_defin (name, def, typ) =
  Rel.Declaration.LocalDef (name, def, typ)

(* Get the name of a rel declaration *)
let rel_name decl =
  Rel.Declaration.get_name decl

(* Get the optional value of a rel declaration *)
let rel_value decl =
  Rel.Declaration.get_value decl

(* Get the type of a rel declaration *)
let rel_type decl =
  Rel.Declaration.get_type decl

(* Map over a rel context with environment kept in synch *)
let map_rel_context env make ctxt =
  Rel.fold_outside
    (fun decl (env, res) ->
       push_rel decl env, (make env decl) :: res)
    ctxt
    ~init:(env, []) |>
  snd

(*
 * Bind all local declarations in the relative context onto the body term as
 * products, substituting away (i.e., zeta-reducing) any local definitions.
 *)
let smash_prod_assum ctxt body =
  Rel.fold_inside
    (fun body decl ->
       match rel_value decl with
       | Some defn -> Vars.subst1 defn body
       | None -> mkProd (rel_name decl, rel_type decl, body))
    ~init:body
    ctxt

(*
 * Bind all local declarations in the relative context onto the body term as
 * lambdas, substituting away (i.e., zeta-reducing) any local definitions.
 *)
let smash_lam_assum ctxt body =
  Rel.fold_inside
    (fun body decl ->
       match rel_value decl with
       | Some defn -> Vars.subst1 defn body
       | None -> mkLambda (rel_name decl, rel_type decl, body))
    ~init:body
    ctxt

(*
 * Decompose the first n product bindings, zeta-reducing let bindings to reveal
 * further product bindings when necessary.
 *)
let decompose_prod_n_zeta n term =
  assert (n >= 0);
  let rec aux n ctxt body =
    if n > 0 then
      match Constr.kind body with
      | Prod (name, param, body) ->
        aux (n - 1) (Rel.add (rel_assum (name, param)) ctxt) body
      | LetIn (name, def_term, def_type, body) ->
        aux n ctxt (Vars.subst1 def_term body)
      | _ ->
        invalid_arg "decompose_prod_n_zeta: not enough products"
    else
      ctxt, body
  in
  aux n Rel.empty term

(*
 * Decompose the first n lambda bindings, zeta-reducing let bindings to reveal
 * further lambda bindings when necessary.
 *)
let decompose_lam_n_zeta n term =
  assert (n >= 0);
  let rec aux n ctxt body =
    if n > 0 then
      match Constr.kind body with
      | Lambda (name, param, body) ->
        aux (n - 1) (Rel.add (rel_assum (name, param)) ctxt) body
      | LetIn (name, def_term, def_type, body) ->
        Vars.subst1 def_term body |> aux n ctxt
      | _ ->
        invalid_arg "decompose_lam_n_zeta: not enough lambdas"
    else
      ctxt, body
  in
  aux n Rel.empty term

(* Is the named declaration an assumption? *)
let is_named_assum = Named.Declaration.is_local_assum

(* Is the named declaration a definition? *)
let is_named_defin = Named.Declaration.is_local_def

(* Make the named declaration for a local assumption *)
let named_assum (id, typ) =
  Named.Declaration.LocalAssum (id, typ)

(* Make the named declaration for a local definition *)
let named_defin (id, def, typ) =
  Named.Declaration.LocalDef (id, def, typ)

(* Get the name of a named declaration *)
let named_ident decl =
  Named.Declaration.get_id decl

(* Get the optional value of a named declaration *)
let named_value decl =
  Named.Declaration.get_value decl

(* Get the type of a named declaration *)
let named_type decl =
  Named.Declaration.get_type decl

(* Map over a named context with environment kept in synch *)
let map_named_context env make ctxt =
  Named.fold_outside
    (fun decl (env, res) ->
       push_named decl env, (make env decl) :: res)
    ctxt
    ~init:(env, []) |>
  snd

(* Lookup n rels and remove then *)
let lookup_pop (n : int) (env : env) =
  let rels = List.map (fun i -> lookup_rel i env) (from_one_to n) in
  (pop_rel_context n env, rels)

let force_constant_body const_body =
  match const_body.const_body with
  | Def const_def ->
    Mod_subst.force_constr const_def
  | OpaqueDef opaq ->
    Opaqueproof.force_proof (Global.opaque_tables ()) opaq
  | _ ->
    CErrors.user_err ~hdr:"force_constant_body"
      (Pp.str "An axiom has no defining term")

(* Lookup a definition *)
let lookup_definition (env : env) (def : types) : types =
  match kind def with
  | Const (c, u) -> force_constant_body (lookup_constant c env)
  | Ind _ -> def
  | _ -> failwith "not a definition"

(* Fully lookup a def in env, but return the term if it is not a definition *)
let rec unwrap_definition (env : env) (trm : types) : types =
  try
    unwrap_definition env (lookup_definition env trm)
  with _ ->
    trm

(* Get the type of an inductive type *)
let type_of_inductive env index mutind_body : types =
  let ind_bodies = mutind_body.mind_packets in
  let ind_body = Array.get ind_bodies index in
  let univs = Declareops.inductive_polymorphic_context mutind_body in
  let univ_instance = Univ.make_abstract_instance univs in
  let mutind_spec = (mutind_body, ind_body) in
  Inductive.type_of_inductive env (mutind_spec, univ_instance)

(*
 * Inductive types create bindings that we need to push to the environment
 * This function gets those bindings
 *)
let bindings_for_inductive env mutind_body ind_bodies : CRD.t list =
  Array.to_list
    (Array.mapi
       (fun i ind_body ->
         let name_id = ind_body.mind_typename in
         let typ = type_of_inductive env i mutind_body in
         CRD.LocalAssum (Name name_id, typ))
       ind_bodies)

(*
 * Similarly but for fixpoints
 *)
let bindings_for_fix (names : name array) (typs : types array) : CRD.t list =
  Array.to_list
    (CArray.map2_i
       (fun i name typ -> CRD.LocalAssum (name, Vars.lift i typ))
       names typs)

(* Find the offset of some environment from some number of parameters *)
let new_rels env npm = nb_rel env - npm

(* Find the offset between two environments *)
let new_rels2 env1 env2 = nb_rel env1 - nb_rel env2

(* Append two contexts (inner first, outer second), shifting internal indices. *)
let context_app inner outer =
  List.append
    (Termops.lift_rel_context (Rel.length outer) inner)
    outer

(* Bind the declarations of a local context as product/let-in bindings *)
let recompose_prod_assum decls term =
  let bind term decl = Term.mkProd_or_LetIn decl term in
  Rel.fold_inside bind ~init:term decls

(* Bind the declarations of a local context as lambda/let-in bindings *)
let recompose_lam_assum decls term =
  let bind term decl = Term.mkLambda_or_LetIn decl term in
  Rel.fold_inside bind ~init:term decls

(* Instantiate an abstract universe context *)
let inst_abs_univ_ctx abs_univ_ctx =
  (* Note that we're creating *globally* fresh universe levels. *)
  Universes.fresh_instance_from_context abs_univ_ctx |> Univ.UContext.make

(* --- Basic questions about terms --- *)

(*
 * Get the arity of a function or function type
 *)
let rec arity p =
  match kind p with
  | Lambda (_, _, b) ->
     1 + arity b
  | Prod (_, _, b) ->
     1 + arity b
  | _ ->
     0

(* Check whether trm applies f (using equal for equality) *)
let applies (f : types) (trm : types) =
  match kind trm with
  | App (g, _) ->
     equal f g
  | _ ->
     false

(* Check whether trm is trm' or applies trm', using equal *)
let is_or_applies (trm' : types) (trm : types) : bool =
  applies trm' trm || equal trm' trm

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

(* Versions over two terms *)
let are_or_apply (trm : types) = and_p (is_or_applies trm)
let apply (trm : types) = and_p (applies trm)

(* --- Inductive types and their eliminators --- *)

(* Don't support mutually inductive or coinductive types yet *)
let check_inductive_supported mutind_body : unit =
  let ind_bodies = mutind_body.mind_packets in
  if Array.length ind_bodies > 1 then
    CErrors.user_err (Pp.str "Mutually inductive types are not supported")
  else if (mutind_body.mind_finite = Declarations.CoFinite) then
    CErrors.user_err (Pp.str "Coinductive types are not supported")

(*
 * Check if a constant is an inductive elminator
 * If so, return the inductive type
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
        lookup_mind ind_name env;
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
 * Boolean version of above that doesn't care about the term type
 *)
let is_elim (env : env) (trm : types) =
  isConst trm && Option.has_some (inductive_of_elim env (destConst trm))

(* Lookup the eliminator over the type sort *)
let type_eliminator (env : env) (ind : inductive) =
  Universes.constr_of_global (Indrec.lookup_eliminator ind InType)

(* Applications of eliminators *)
type elim_app =
  {
    elim : types;
    pms : types list;
    p : types;
    cs : types list;
    final_args : types list;
  }

(* Apply an eliminator *)
let apply_eliminator (ea : elim_app) : types =
  let args = List.append ea.pms (ea.p :: ea.cs) in
  mkAppl (mkAppl (ea.elim, args), ea.final_args)

(* Deconstruct an eliminator application *)
let deconstruct_eliminator env evd app : elim_app =
  let elim = first_fun app in
  let ip_args = unfold_args app in
  let ip_typ = reduce_type env evd elim in
  let from_i = Option.get (inductive_of_elim env (destConst elim)) in
  let from_m = lookup_mind from_i env in
  let npms = from_m.mind_nparams in
  let from_arity = arity (type_of_inductive env 0 from_m) in
  let num_indices = from_arity - npms in
  let num_props = 1 in
  let num_constrs = arity ip_typ - npms - num_props - num_indices - 1 in
  let (pms, pmd_args) = take_split npms ip_args in
  match pmd_args with
  | p :: cs_and_args ->
     let (cs, final_args) = take_split num_constrs cs_and_args in
     { elim; pms; p; cs; final_args }
  | _ ->
     failwith "can't deconstruct eliminator; no final arguments"

(*
 * Given the type of a case of an eliminator,
 * determine the number of inductive hypotheses
 *)
let rec num_ihs env rec_typ typ =
  match kind typ with
  | Prod (n, t, b) ->
     if is_or_applies rec_typ (reduce_term env t) then
       let (n_b_t, b_t, b_b) = destProd b in
       1 + num_ihs (push_local (n, t) (push_local (n_b_t, b_t) env)) rec_typ b_b
     else
       num_ihs (push_local (n, t) env) rec_typ b
  | _ ->
     0

(* Determine whether template polymorphism is used for a one_inductive_body *)
let is_ind_body_template ind_body =
  match ind_body.mind_arity with
  | RegularArity _ -> false
  | TemplateArity _ -> true

(* Construct the arity of an inductive type from a one_inductive_body *)
let arity_of_ind_body ind_body =
  match ind_body.mind_arity with
  | RegularArity { mind_user_arity; mind_sort } ->
    mind_user_arity
  | TemplateArity { template_param_levels; template_level } ->
    let sort = Constr.mkType template_level in
    recompose_prod_assum ind_body.mind_arity_ctxt sort

(* Create an Entries.local_entry from a Rel.Declaration.t *)
let make_ind_local_entry decl =
  let entry =
    match decl with
    | CRD.LocalAssum (_, typ) -> Entries.LocalAssumEntry typ
    | CRD.LocalDef (_, term, _) -> Entries.LocalDefEntry term
  in
  match CRD.get_name decl with
  | Name.Name id -> (id, entry)
  | Name.Anonymous -> failwith "Parameters to an inductive type may not be anonymous"

(* Instantiate an abstract_inductive_universes into an Entries.inductive_universes with Univ.UContext.t *)
let make_ind_univs_entry = function
  | Monomorphic_ind univ_ctx_set ->
    let univ_ctx = Univ.UContext.empty in
    (Entries.Monomorphic_ind_entry univ_ctx_set, univ_ctx)
  | Polymorphic_ind abs_univ_ctx ->
    let univ_ctx = inst_abs_univ_ctx abs_univ_ctx in
    (Entries.Polymorphic_ind_entry univ_ctx, univ_ctx)
  | Cumulative_ind abs_univ_cumul ->
    let abs_univ_ctx = Univ.ACumulativityInfo.univ_context abs_univ_cumul in
    let univ_ctx = inst_abs_univ_ctx abs_univ_ctx in
    let univ_var = Univ.ACumulativityInfo.variance abs_univ_cumul in
    let univ_cumul = Univ.CumulativityInfo.make (univ_ctx, univ_var) in
    (Entries.Cumulative_ind_entry univ_cumul, univ_ctx)

let open_inductive ?(global=false) env (mind_body, ind_body) =
  let univs, univ_ctx = make_ind_univs_entry mind_body.mind_universes in
  let subst_univs = Vars.subst_instance_constr (Univ.UContext.instance univ_ctx) in
  let env = Environ.push_context univ_ctx env in
  if global then
    Global.push_context false univ_ctx;
  let arity = arity_of_ind_body ind_body in
  let arity_ctx = [CRD.LocalAssum (Name.Anonymous, arity)] in
  let ctors_typ = Array.map (recompose_prod_assum arity_ctx) ind_body.mind_user_lc in
  env, univs, subst_univs arity, Array.map_to_list subst_univs ctors_typ

let declare_inductive typename consnames template univs nparam arity constypes =
  let open Entries in
  let params, arity = Term.decompose_prod_n_assum nparam arity in
  let constypes = List.map (Term.decompose_prod_n_assum (nparam + 1)) constypes in
  let ind_entry =
    { mind_entry_typename = typename;
      mind_entry_arity = arity;
      mind_entry_template = template;
      mind_entry_consnames = consnames;
      mind_entry_lc = List.map snd constypes }
  in
  let mind_entry =
    { mind_entry_record = None;
      mind_entry_finite = Declarations.Finite;
      mind_entry_params = List.map make_ind_local_entry params;
      mind_entry_inds = [ind_entry];
      mind_entry_universes = univs;
      mind_entry_private = None }
  in
  let ((_, ker_name), _) = Declare.declare_mind mind_entry in
  let mind = MutInd.make1 ker_name in
  let ind = (mind, 0) in
  Indschemes.declare_default_schemes mind;
  ind

(* --- Basic mapping --- *)

(*
 * Recurse on a mapping function with an environment for a fixpoint
 *)
let map_rec_env_fix map_rec d env a (ns : Name.t array) (ts : types array) =
  let fix_bindings = bindings_for_fix ns ts in
  let env_fix = push_rel_context fix_bindings env in
  let n = List.length fix_bindings in
  let d_n = List.fold_left (fun a' _ -> d a') a (range 0 n) in
  map_rec env_fix d_n

(*
 * Map a function over a term in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let rec map_term_env f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env f d in
  match kind trm with
  | Cast (c, k, t) ->
     let c' = map_rec env a c in
     let t' = map_rec env a t in
     mkCast (c', k, t')
  | Prod (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_local (n, t) env) (d a) b in
     mkProd (n, t', b')
  | Lambda (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_local (n, t) env) (d a) b in
     mkLambda (n, t', b')
  | LetIn (n, trm, typ, e) ->
     let trm' = map_rec env a trm in
     let typ' = map_rec env a typ in
     let e' = map_rec (push_let_in (n, e, typ) env) (d a) e in
     mkLetIn (n, trm', typ', e')
  | App (fu, args) ->
     let fu' = map_rec env a fu in
     let args' = Array.map (map_rec env a) args in
     mkApp (fu', args')
  | Case (ci, ct, m, bs) ->
     let ct' = map_rec env a ct in
     let m' = map_rec env a m in
     let bs' = Array.map (map_rec env a) bs in
     mkCase (ci, ct', m', bs')
  | Fix ((is, i), (ns, ts, ds)) ->
     let ts' = Array.map (map_rec env a) ts in
     let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
     mkFix ((is, i), (ns, ts', ds'))
  | CoFix (i, (ns, ts, ds)) ->
     let ts' = Array.map (map_rec env a) ts in
     let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
     mkCoFix (i, (ns, ts', ds'))
  | Proj (p, c) ->
     let c' = map_rec env a c in
     mkProj (p, c')
  | _ ->
     f env a trm

(*
 * Map a function over a term, when the environment doesn't matter
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let map_term f d (a : 'a) (trm : types) : types =
  map_term_env (fun _ a t -> f a t) d empty_env a trm

(* --- Names --- *)

(* Add a suffix to a name identifier *)
let with_suffix id suffix =
  let prefix = Id.to_string id in
  Id.of_string (String.concat "_" [prefix; suffix])

(* Turn a name into an optional identifier *)
let ident_of_name = function
  | Name id -> Some id
  | Anonymous -> None

(* Turn an identifier into an external (i.e., surface-level) reference *)
let reference_of_ident id =
  Libnames.Ident id |> CAst.make

(* Turn a name into an optional external (i.e., surface-level) reference *)
let reference_of_name =
  ident_of_name %> Option.map reference_of_ident

(* Convert an external reference into a qualid *)
let qualid_of_reference =
  Libnames.qualid_of_reference %> CAst.with_val identity

(* Convert a term into a global reference with universes (or raise Not_found) *)
let pglobal_of_constr term =
  match Constr.kind term with
  | Const (const, univs) -> ConstRef const, univs
  | Ind (ind, univs) -> IndRef ind, univs
  | Construct (cons, univs) -> ConstructRef cons, univs
  | Var id -> VarRef id, Univ.Instance.empty
  | _ -> raise Not_found

(* Convert a global reference with universes into a term *)
let constr_of_pglobal (glob, univs) =
  match glob with
  | ConstRef const -> mkConstU (const, univs)
  | IndRef ind -> mkIndU (ind, univs)
  | ConstructRef cons -> mkConstructU (cons, univs)
  | VarRef id -> mkVar id

type global_substitution = global_reference Globmap.t

(* Substitute global references throughout a term *)
let subst_globals subst term =
  let rec aux term =
    try
      pglobal_of_constr term |>
      map_puniverses (flip Globmap.find subst) |>
      constr_of_pglobal
    with Not_found ->
      Constr.map aux term
  in
  aux term

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
 * Declare a new inductive family under the given name with the transformed type
 * arity and constructor types from the given inductive definition. Names for
 * the constructors remain the same.
 *
 * NOTE: Global side effects.
 *)
let transform_inductive ident tr_constr ((mind_body, ind_body) as ind_specif) =
  (* TODO: Can we re-use this for ornamental lifting of inductive families? *)
  let env = Global.env () in
  let env, univs, arity, cons_types =
    open_inductive ~global:true env ind_specif
  in
  let evm = ref (Evd.from_env env) in
  let arity' = tr_constr env evm arity in
  let cons_types' = List.map (tr_constr env evm) cons_types in
  declare_inductive
    ident (Array.to_list ind_body.mind_consnames)
    (is_ind_body_template ind_body) univs
    mind_body.mind_nparams arity' cons_types'

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
