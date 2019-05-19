(*
 * Translation of fixpoints and match statements to induction principles.
 * By Nate Yazdani, taken from the DEVOID code.
 *)

open Util
open Names
open Univ
open Context
open Term
open Constr
open Inductiveops
open CErrors
open Coqterms
open Abstraction

(* --- Begin DEVOID library code --- *)
       
(*
 * When we merge PUMPKIN with DEVOID, these will move into
 * coqterms in the library. For now, that doesn't make sense
 * with the current organization of coqterms.
 *)
       
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
                           
(* --- End DEVOID library code --- *)

(*
 * Pair the outputs of two functions on the same input.
 *)
let pair f g =
  fun x -> f x, g x

(*
 * Convenient wrapper around Vars.liftn shift (skip + 1) term.
 *)
let lift_rels ?(skip=0) shift term =
  Vars.liftn shift (skip + 1) term

(*
 * Same as lift_rels ~skip:skip 1.
 *)
let lift_rel ?(skip=0) = lift_rels ~skip:skip 1

(*
 * Convenient wrapper around Vars.liftn (-shift) (skip + 1) term.
 *)
let drop_rels ?(skip=0) shift term =
  assert (Vars.noccur_between (skip + 1) (skip + shift) term);
  Vars.liftn (-shift) (skip + 1) term

(*
 * Same as drop_rels ~skip:skip 1.
 *)
let drop_rel ?(skip=0) = drop_rels ~skip:skip 1

(*
 * Function from: 
 * https://github.com/coq/coq/commit/7ada864b7728c9c94b7ca9856b6b2c89feb0214e
 * Inlined here to make this compatible with Coq 8.8.0
 *)
let fold_constr_with_binders g f n acc c =
  match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g  n) (f n acc t) c
  | Lambda (na,t,c) -> f (g  n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g  n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (p,c) -> f n acc c
  | Evar (_,l) -> Array.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2 (fun c n t -> g c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2 (fun c n t -> g c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
                                   
(*
 * Gather the set of relative (de Bruijn) variables occurring in the term that
 * are free (i.e., not bound) under nb levels of external relative binding.
 *
 * Use free_rels 0 Int.Set.empty if you do not wish to filter out any free
 * relative variables below a certain binding level (nb) or supply the initial
 * accumulator (frels).
 *
 * Examples:
 * - free_rels 0 {} (Lambda(_, Rel 2, App(Rel 2, [Rel 1; Rel 4]))) = { 1, 2, 3 }
 * - free_rels 1 {} (Lambda(_, Rel 2, App(Rel 2, [Rel 1; Rel 4]))) = { 2, 3 }
 * - free_rels 2 {} (Lambda(_, Rel 2, App(Rel 2, [Rel 1; Rel 4]))) = { 3 }
 *)
let rec free_rels nb frels term =
  match Constr.kind term with
  | Rel i ->
    if i > nb then Int.Set.add (Debruijn.unshift_i_by nb i) frels else frels
  | _ ->
    fold_constr_with_binders succ free_rels nb frels term

(*
 * Give a "reasonable" name to each anonymous local declaration in the relative
 * context. Name generation is according to standard Coq policy (cf., Namegen)
 * and does not guarantee freshness, but term type-checking is only sensitive to
 * anonymity. (Names are freshened by subscription when printed.)
 *)
let deanonymize_context env evm ctxt =
  List.map EConstr.of_rel_decl ctxt |>
  Namegen.name_context env evm |>
  List.map (EConstr.to_rel_decl evm)

(*
 * Instantiate a local assumption as a local definition, using the provided term
 * as its definition.
 *
 * Raises an assertion error if the local declaration is not a local assumption.
 *)
let define_rel_decl body decl =
  assert (is_rel_assum decl);
  rel_defin (rel_name decl, body, rel_type decl)

(*
 * Extract the components of an inductive type: the (universe-instantiated)
 * inductive name, the sequence of parameters, and the sequence of indices.
 *)
let decompose_indvect ind_type =
  let pind, args = decompose_appvect ind_type |> on_fst destInd in
  let nparam = inductive_nparams (out_punivs pind) in
  let params, indices = Array.chop nparam args in
  pind, params, indices

(*
 * Same as decompose_indvect but converts the result arrays into lists.
 *)
let decompose_ind ind_type =
  decompose_indvect ind_type |> on_pi2 Array.to_list |> on_pi3 Array.to_list

(*
 * Construct a relative context, consisting of only local assumptions,
 * quantifying over instantiations of the inductive family.
 *
 * In other words, the output relative context assumes all indices (in standard
 * order) and then a value of the inductive type (at those indices).
 *
 * Note that an inductive family is an inductive name with parameter terms.
 *)
let build_inductive_context env ind_fam ind_name =
  let ind_type = build_dependent_inductive env ind_fam in
  let ind_decl = rel_assum (ind_name, ind_type) in
  get_arity env ind_fam |> fst |> Rel.add ind_decl |> Termops.smash_rel_context

(*
 * Transform the relative context of a fixed-point function into a form suitable
 * for simple recursion (i.e., eliminator-style quantification).
 *
 * The transformed relative context only satisfies that guarantee (or even
 * well-formedness) when immediately preceded by the quantifying relative
 * context for the inductive type and then by a wrapping relative context
 * for the fixed point.
 *)
let build_recursive_context fix_ctxt params indices =
  let nb = Rel.length fix_ctxt in (* length of fixed-point context *)
  let nb' = nb + List.length indices + 1 in (* length of recursive context *)
  let par_rels = List.fold_left (free_rels 0) Int.Set.empty params in
  let idx_rels = 1 :: List.rev_map destRel indices in
  (* NOTE: DestKO raised (above) if any index was not bound fully abstracted. *)
  let is_rec i = i <= nb in
  let is_par i = not (Int.Set.mem i par_rels) in (* parameter independence *)
  assert (List.for_all is_rec idx_rels); (* Is every index bound recursively? *)
  assert (List.distinct idx_rels); (* Are the indices bound separately and... *)
  assert (List.for_all is_par idx_rels); (* ...independently of parameters? *)
  (* Abstract inductive quantification to the outer inductive context *)
  let buf = Termops.lift_rel_context nb' fix_ctxt |> Array.of_list in
  let abstract_rel j i = buf.(i - 1) <- define_rel_decl (mkRel j) buf.(i - 1) in
  (* Abstract each parameter-relevant binding to the wrapper context. *)
  Int.Set.iter (abstract_rel nb') (Int.Set.filter is_rec par_rels);
  (* Abstract the remaining inductive bindings to the eliminator context. *)
  List.iter2 abstract_rel (List.map_i (-) (nb + 1) idx_rels) idx_rels;
  Array.to_list buf

(*
 * Build the minor premise for elimination at a constructor from the
 * corresponding fixed-point case.
 *
 * In particular, insert recurrence bindings (for inductive hypotheses) in the
 * appropriate positions, substituting recursive calls with the recurrence
 * binding its value.
 *
 * The last argument provides the case's parameter context (quantifying
 * constructor arguments) with the case's body term.
 *)
let premise_of_case env ind_fam (ctxt, body) =
  let nb = Rel.length ctxt in
  let ind_head = dest_ind_family ind_fam |> on_fst mkIndU |> applist in
  let fix_name, fix_type = Environ.lookup_rel 1 env |> pair rel_name rel_type in
  let insert_recurrence i body decl =
    let i = Debruijn.unshift_i_by i nb in
    let j = Debruijn.shift_i i in
    let body' =
      match eq_constr_head (lift_rels i ind_head) (rel_type decl) with
      | Some indices ->
        assert (is_rel_assum decl);
        let args = Array.append (Array.map lift_rel indices) [|mkRel 1|] in
        let rec_type = prod_appvect (lift_rels j fix_type) args in
        let fix_call = mkApp (mkRel j, args) in
        mkLambda (fix_name, rec_type, abstract_subterm fix_call body)
      | _ ->
        body
    in
    mkLambda_or_LetIn decl body'
  in
  List.fold_left_i insert_recurrence 0 body ctxt

(*
 * Given a constructor summary (cf., Inductiveops), build a parameter context
 * to quantify over constructor arguments (and thus values of that constructor)
 * and partially evaluate the functional applied to the constructed value's type
 * indices and (subsequently) to the constructed value itself.
 *
 * Partial evaluation reduces to beta/iota-normal form. Exclusion of delta
 * reduction is intentional (rarely beneficial, usually detrimental).
 *)
let split_case env evm fun_term cons_sum =
  let cons = build_dependent_constructor cons_sum in
  let env = Environ.push_rel_context cons_sum.cs_args env in
  let body =
    let head = lift_rels cons_sum.cs_nargs fun_term in
    let args = Array.append cons_sum.cs_concl_realargs [|cons|] in
    mkApp (head, args) |> Reduction.nf_betaiota env
  in
  deanonymize_context env evm cons_sum.cs_args, body

(*
 * Eta-expand a case term according to the corresponding constructor's type.
 *)
let expand_case env evm case_term cons_sum =
  let body =
    let head = lift_rels cons_sum.cs_nargs case_term in
    let args = Rel.to_extended_list mkRel 0 cons_sum.cs_args in
    Reduction.beta_applist head args
  in
  deanonymize_context env evm cons_sum.cs_args, body

(*
 * Build an elimination head (partially applied eliminator) including the
 * parameters and (sort-adjusted) motive for the given inductive family and
 * (dependent) elimination type.
 *
 * The sorts of the inductive family and of the elimination type are considered,
 * respectively, when adjusting the elimination type into a motive (by removing
 * dependency for Prop-sorted inductive families) and when selecting one of the
 * inductive family's eliminators.
 *
 * NOTE: Motive adjustment might be too overzealous; under some particular
 * conditions, Coq does allow dependency in the elimination motive for a Prop-
 * sorted inductive family.
 *)
let configure_eliminator env evm ind_fam typ =
  let ind, params = dest_ind_family ind_fam |> on_fst out_punivs in
  let nb = inductive_nrealargs ind + 1 in
  let typ_ctxt, typ_body =
    let typ_ctxt, typ_body = decompose_prod_n_assum nb typ in
    let ind_sort = get_arity env ind_fam |> snd in
    if Sorts.family_equal ind_sort Sorts.InProp then
      List.tl typ_ctxt, drop_rel typ_body
    else
      typ_ctxt, typ_body
  in
  let elim =
    let typ_env = Environ.push_rel_context typ_ctxt env in
    let typ_sort = e_infer_sort typ_env evm typ_body in
    Indrec.lookup_eliminator ind typ_sort |> e_new_global evm
  in
  let motive = recompose_lam_assum typ_ctxt typ_body in
  mkApp (elim, Array.append (Array.of_list params) [|motive|])

(*
 * Translate a fixed-point function using simple recursion (i.e., quantifying
 * the inductive type like an eliminator) into an elimination form.
 *)
let desugar_recursion env evm ind_fam fix_name fix_type fix_term =
  (* Build the elimination head (eliminator with parameters and motive) *)
  let elim_head = configure_eliminator env evm ind_fam fix_type in
  (* Build the minor premises *)
  let premises =
    let fix_env = Environ.push_rel (rel_assum (fix_name, fix_type)) env in
    let build_premise cons_sum =
      lift_constructor 1 cons_sum |> split_case fix_env !evm fix_term |>
      premise_of_case fix_env ind_fam |> drop_rel
    in
    get_constructors env ind_fam |> Array.map build_premise
  in
  mkApp (elim_head, premises)

(*
 * Translate a fixed-point function into an elimination form.
 *
 * This function works by transforming the fixed point to use simple recursion
 * (i.e., to quantify the inductive type like a dependent eliminator), calling
 * desugar_recusion, and then wrapping the translated elimination form to conform
 * to the original fixed point's type.
 *
 * Note that the resulting term will not satisfy definitional equality with the
 * original term but should satisfy most (all?) definitional equalities when
 * applied to all indices and a head-canonical discriminee. Still, this could
 * impact the well-typedness of inductive proof terms, particularly when
 * rewriting the unrolled recursive function by an inductive hypothesis. We will
 * know more after testing compositional translation of a complete module, which
 * will avoid incidental mixtures of the old version (by named constant) and the
 * new version (by expanded definition). (Such incidental mixtures arise, for
 * example, in some of the List module's proofs regarding the In predicate.)
 *)
let desugar_fixpoint env evm fix_pos fix_name fix_type fix_term =
  let nb = fix_pos + 1 in (* number of bindings guarding recursion *)
  (* Pull off bindings through the parameter guarding structural recursion *)
  let fix_ctxt, fix_type = decompose_prod_n_zeta nb fix_type in
  let _, fix_term = decompose_lam_n_zeta nb fix_term in
  (* Gather information on the inductive type for recursion/elimination *)
  let ind_name, ind_type = Rel.lookup 1 fix_ctxt |> pair rel_name rel_type in
  let pind, params, indices = decompose_ind (lift_rel ind_type) in
  let ind_fam = make_ind_family (pind, params) in
  let env = Environ.push_rel_context fix_ctxt env in (* for eventual wrapper *)
  let rec_ctxt, rec_args = (* quantify the inductive type like an eliminator *)
    let ind_ctxt = build_inductive_context env ind_fam ind_name in
    let fun_ctxt = build_recursive_context fix_ctxt params indices in
    fun_ctxt @ ind_ctxt,
    Array.of_list (indices @ (mkRel 1) :: Rel.to_extended_list mkRel 0 fun_ctxt)
  in
  let nb' = Rel.length rec_ctxt in
  let k = Debruijn.unshift_i_by nb nb' in (* always more bindings than before *)
  let rec_type =
    fix_type |> lift_rels ~skip:nb nb |> (* for external wrapper *)
    lift_rels ~skip:nb k |> smash_prod_assum rec_ctxt
  in
  let rec_term =
    let nb_rec = Debruijn.shift_i nb in (* include self reference *)
    let rec_env = Environ.push_rel (rel_assum (fix_name, rec_type)) env in
    let rec_ctxt = Termops.lift_rel_context 1 rec_ctxt in
    let fix_self = (* wrapper to adjust arguments for a recursive call *)
      recompose_lam_assum
        (Termops.lift_rel_context nb_rec fix_ctxt)
        (mkApp (mkRel nb_rec, rec_args))
    in
    fix_term |> lift_rels ~skip:nb_rec nb |> (* for external wrapper *)
    lift_rels ~skip:nb k |> smash_lam_assum rec_ctxt |>
    lift_rel ~skip:1 |> Vars.subst1 fix_self |> Reduction.nf_betaiota rec_env
  in
  (* Desugar the simple recursive function into an elimination form *)
  let rec_elim = desugar_recursion env evm ind_fam fix_name rec_type rec_term in
  (* Wrap the elimination form to reorder initial arguments *)
  recompose_lam_assum fix_ctxt (mkApp (rec_elim, rec_args))

(*
 * Given the components of a match expression, build an equivalent elimination
 * expression. The resulting term will not use any recurrence (i.e., inductive
 * hypothesis) bound in the minor elimination premises (i.e., case functions),
 * since the original term was non-recursive.
 *
 * Note that the resulting term may not satisfy definitional equality with the
 * original term, as Coq lacks eta-conversion between a non-recursive function
 * and its fixed point (i.e., f =\= fix[_.f]). Definitional equality should hold
 * (at least) when the discriminee term is head-canonical.
 *)
let desugar_match env evm info pred discr cases =
  let typ = lambda_to_prod pred in
  let pind, params, indices = decompose_indvect (e_infer_type env evm discr) in
  let ind_fam = make_ind_family (pind, Array.to_list params) in
  let elim_head = configure_eliminator env evm ind_fam typ in
  let premises =
    let fix_env = Environ.push_rel (rel_assum (Name.Anonymous, typ)) env in
    let cases = Array.map lift_rel cases in
    let build_premise cons_case cons_sum =
      lift_constructor 1 cons_sum |> expand_case fix_env !evm cons_case |>
      premise_of_case fix_env ind_fam |> drop_rel
    in
    get_constructors fix_env ind_fam |> Array.map2 build_premise cases
  in
  mkApp (elim_head, Array.concat [premises; indices; [|discr|]])

(*
 * Translate the given term into an equivalent, bisimulative (i.e., homomorpic
 * reduction behavior) version using eliminators instead of match or fix
 * expressions.
 *
 * Mutual recursion, co-recursion, and universe polymorphism are not supported.
 *)
let desugar_constr env evm term =
  let rec aux env term =
    match Constr.kind term with
    | Lambda (name, param, body) ->
      let param' = aux env param in
      let body' = aux (push_local (name, param') env) body in
      mkLambda (name, param', body')
    | Prod (name, param, body) ->
      let param' = aux env param in
      let body' = aux (push_local (name, param') env) body in
      mkProd (name, param', body')
    | LetIn (name, local, annot, body) ->
      let local' = aux env local in
      let annot' = aux env annot in
      let body' = aux (push_let_in (name, local', annot') env) body in
      mkLetIn (name, local', annot', body')
    | Fix (([|fix_pos|], 0), ([|fix_name|], [|fix_type|], [|fix_term|])) ->
      desugar_fixpoint env evm fix_pos fix_name fix_type fix_term |> aux env
    | Fix _ ->
      user_err ~hdr:"desugar" (Pp.str "mutual recursion not supported")
    | CoFix _ ->
      user_err ~hdr:"desugar" (Pp.str "co-recursion not supported")
    | Case (info, pred, discr, cases) ->
      desugar_match env evm info pred discr cases |> aux env
    | _ ->
      Constr.map (aux env) term
  in
  let term' = aux env term in
  ignore (e_infer_type env evm term'); (* to infer universe constraints *)
  term'
