(* Logic for proof categories that is specific to terms and types *)

open Stateutils
open Constr
open Environ
open Proofcat
open Names
open Debruijn
open Assumptions
open Utilities
open Evd

module CRD = Context.Rel.Declaration

(* --- Construction --- *)

(* Get the extension for a trm in env *)
let ext_of_term (env : env) (trm : types) : extension =
  LazyBinding (trm, env)

(* Get a fresh inductive hypothesis *)
let fresh_ih (_ : unit) : extension =
  InductiveHypothesis (fid ())

(* --- Destruction --- *)

(* Get the term from ext *)
let rec ext_term (ext : extension) : types =
  match ext with
  | Index i ->
     mkRel i
  | AnonymousBinding ->
     failwith "term is anonymous"
  | AppBinding (e1, e2) ->
     mkApp (ext_term e1, Array.of_list [ext_term e2])
  | LazyBinding (trm, _) ->
     trm
  | _ ->
     failwith "not a term"

(* Check whether an extension represents a lambda term *)
let ext_is_lambda (e : extension) : bool =
  match e with
  | LazyBinding (trm, env) -> isLambda trm
  | _ -> false

(* Check whether an extension represents an inductive hypothesis *)
let ext_is_ih (e : extension) : bool =
  match e with
  | InductiveHypothesis _ -> true
  | _ -> false

(* Check whether an arrow represents an inductive hypothesis *)
let arrow_is_ih (m : arrow) : bool =
  let (_, e, _) = m in
  ext_is_ih e

(* Get the environment from a context *)
let context_env (co : context_object) : env =
  let Context (ctx, i) = co in
  match ctx with
  | Term (trm, env) -> env
  | _ -> failwith "context is not a term"

(* Get the term from a context *)
let context_term (co : context_object) : types =
  let Context (ctx, i) = co in
  match ctx with
  | Term (trm, env) -> trm
  | _ -> failwith "context is not a term"

(* Destruct a context that is a term *)
let dest_context_term (co : context_object) : types * env =
  (context_term co, context_env co)

(* Get the index of a context *)
let context_index (co : context_object) : int =
  let Context (ctx, i) = co in i

(* Check whether a context is a term representing a product *)
let context_is_product (co : context_object) : bool =
  let Context (ctx, i) = co in
  match ctx with
  | Term (trm, env) -> isProd trm
  | Gamma -> false

(* Get the product type for a context that is a term representing a product *)
let context_as_product (co : context_object) : Name.t * types * types =
  let Context (ctx, i) = co in
  match ctx with
  | Term (trm, env) -> destProd trm
  | Gamma -> assert false

(* Check whether a context is a term represent an application *)
let context_is_app (co : context_object) : bool =
  let Context (ctx, i) = co in
  match ctx with
  | Term (trm, env) -> isApp trm
  | Gamma -> false

(* Get the function and args for a context that is a term representing an application *)
let context_as_app (co : context_object) : types * types array =
  let Context (ctx, i) = co in
  match ctx with
  | Term (trm, env) -> destApp trm
  | Gamma -> assert false

(*
 * Get the subpath that is common to all paths
 * That is, the place where all paths intersect
 *
 * This is only guaranteed to work for inductive proofs
 * Results are otherwise undefined
 * When we test, we should see what happens otherwise
 * Then return empty list
 * Then in params_and_prop, test for that and error
 *)
let unique_common_subpath (paths : arrow list list) =
  fold_left_state
    (fun l path ->
      match l with
      | [] -> ret path
      | _ -> filter_state (fun m -> contains_arrow m path) l)
    []
    paths

(*
 * From a proof category that represents an inductive proof, get
 * the inductive parameters and the inductive property
 *
 * Not sure about reversal
 *)
let params_and_prop (c : proof_cat) (npms : int) =
  let i = initial c in
  bind
    (paths_from c i)
    (fun paths ->   
      if List.length paths = 1 then
        let path = Array.of_list (List.hd paths) in
        let subpath = List.rev (List.map (Array.get path) (range 0 (npms + 1))) in
        ret (List.rev (List.tl subpath), List.hd subpath)
      else
        bind
          (unique_common_subpath paths)
          (fun l -> ret (let l = List.rev l in (List.tl l, List.hd l))))

(*
 * From a proof category that represents an inductive proof, get
 * the inductive parameters
 *)
let params (c : proof_cat) (npms : int) =
  bind (params_and_prop c npms) (fun pair -> ret (fst pair))

(*
 * From a proof category that represents an inductive proof,
 * get the inductive property
 *)
let prop (c : proof_cat) (npms : int) =
  bind (params_and_prop c npms) (fun pair -> ret (snd pair))

(*
 * Get the only extension in a proof category as a term
 * Fail if there are no extensions
 * Fail if there are multiple extensions
 *)
let only_extension_as_term (c : proof_cat) : types =
  map_ext ext_term (only_arrow c)

(*
 * Given a proof category with several paths,
 * construct several proof categories, each with one path.
 *)
let split (c : proof_cat) =
  let i = initial c in
  bind
    (paths_from c i)
    (map_state
       (fun ms sigma ->
         let os = i :: (conclusions ms) in
         let (_, _, t) = List.nth ms (List.length ms - 1) in
         make_category os ms (Some i) (Some t) sigma))

(* --- Transformations on terms and environments --- *)

(*
 * Curry a lambda extension
 * Fail if it is not a lambda
 *)
let curry_lambda (e : extension) : extension =
  assert (ext_is_lambda e);
  let LazyBinding (trm, env) = e in
  let (n, t, b) = destLambda trm in
  ext_of_term (push_rel CRD.(LocalAssum(n, t)) env) b

(* --- Finding terms and environments --- *)

(* Check if c has an inductive hypothesis *)
let has_ihs (c : proof_cat) : bool =
  List.exists arrow_is_ih (morphisms c)

(* Find the inductive hypotheses in c *)
let find_ihs (c : proof_cat) : arrow list =
  List.filter arrow_is_ih (morphisms c)

(* Find the distance to the closest IH to m given a list of IHs *)
let closest_ih c (ihs : arrow list) (m : arrow) =
  let (s, _, _) = m in
  bind
    (map_state
      (map_dest
         (fun d ->
           bind (arrows_between c d s) (fun path -> ret (d, List.length path))))
      ihs)
    (fun ih_distances ->
      let ih_distances_sorted =
        List.sort
          (fun (_, i1) (_, i2) -> Pervasives.compare i1 i2)
          ih_distances
      in ret (List.hd ih_distances_sorted))

(* Determine which arrow is closer to an IH *)
let closer_to_ih c (ihs : arrow list) (m1 : arrow) (m2 : arrow) sigma : int state =
  let sigma, (m1_ih_dst, m1_ih_prox) = closest_ih c ihs m1 sigma in
  let sigma, (m2_ih_dst, m2_ih_prox) = closest_ih c ihs m2 sigma in
  let ih_1_index = shortest_path_length c m1_ih_dst in
  let ih_2_index = shortest_path_length c m2_ih_dst in
  if m1_ih_prox = m2_ih_prox then
    sigma, Pervasives.compare ih_1_index ih_2_index (* start lower *)
  else
    sigma, Pervasives.compare m1_ih_prox m2_ih_prox (* start closer to IH *)

(*
 * Sort cs so that the base cases are first in the list
 *)
let base_cases_first (cs : proof_cat list) : proof_cat list =
  List.stable_sort
    (fun c1 c2 ->
      let c1_is_ind = has_ihs c1 in
      let c2_is_ind = has_ihs c2 in
      if c1_is_ind && (not c2_is_ind) then
        1
      else if (not c1_is_ind) && c2_is_ind then
        - 1
      else
        0)
    cs

(* --- Debruijn --- *)

(* Unshifts the index of an extension if it is not locally bound *)
let rec unshift_ext_local (max_local_binding : int) (rel_adjust : int) (e : extension) : extension =
  match e with
  | Index i ->
      let i' = if (i > max_local_binding) then unshift_i_by rel_adjust i else i in
      Index i'
  | LazyBinding (trm, env) ->
      let trm' = unshift_local max_local_binding rel_adjust trm in
      let env' = unshift_env_by rel_adjust env in
      LazyBinding (trm', env')
  | AppBinding (e1, e2) ->
      let e1' = unshift_ext_local max_local_binding rel_adjust e1 in
      let e2' = unshift_ext_local max_local_binding rel_adjust e2 in
      AppBinding (e1', e2')
  | _ ->
     e

(* Unshifts the index of an extension *)
let rec unshift_ext_by (n : int) (e : extension) : extension =
  match e with
  | Index i ->
      let i' = unshift_i_by n i in
      Index i'
  | LazyBinding (trm, env) ->
      let trm' = unshift_by n trm in
      let env' = unshift_env_by n env in
      LazyBinding (trm', env')
  | AppBinding (e1, e2) ->
      let e1' = unshift_ext_by n e1 in
      let e2' = unshift_ext_by n e2 in
      AppBinding (e1', e2')
  | _ ->
     e

(*
 * Shifts the index of an extension
 *
 * When we test: There's a bug here (and possibly elsewhere) when you
 * unshift and then shift, since it uses local which has a gt 0 clause
 * Could maybe use min_int, but then have to be consistent, including
 * in env, which right now doesn't have a local version.
 *)
let shift_ext_by (n : int) (e : extension) : extension =
  unshift_ext_by (- n) e

(* --- Identifiers --- *)

(* Map the identifiers of contexts of c with f *)
let map_ids (f : int -> int) (c : proof_cat) =
  apply_functor
    (fun (Context (c, id)) ->
      ret (Context (c, f id)))
    (fun (Context (s, sid), e, Context (d, did)) ->
      ret (Context (s, f sid), e, Context (d, f did)))
    c

(* Get a map from context identifiers to fresh identifiers *)
let get_fresh_ids (c : proof_cat) =
  bind (objects c) (map_state (fun (Context (_, id)) -> ret (id, (fid ()))))

(*
 * Make fresh identifiers for every context in c
 *)
let make_all_fresh (c : proof_cat) =
  bind (get_fresh_ids c) (fun fids -> map_ids (fun id -> List.assoc id fids) c)

(* --- Substitution --- *)

(* Substitute in parameters for inductive types in an extension *)
let rec substitute_ext_params (subs : param_substitutions) (e : extension) : extension =
  match e with
  | Index i ->
     Index (destRel (substitute_params subs (mkRel i)))
  | LazyBinding (trm, env) ->
     let trm' = substitute_params subs trm in
     let env' = substitute_env_params subs env in
     LazyBinding(trm', env')
  | AppBinding (e1, e2) ->
     let e1' = substitute_ext_params subs e1 in
     let e2' = substitute_ext_params subs e2 in
     AppBinding (e1', e2')
  | _ -> e

(*
 * Substitute env for the environment in e
 *)
let rec substitute_ext_env (env : env) (e : extension) : extension =
  match e with
  | LazyBinding (trm, _) ->
      LazyBinding (trm, env)
  | AppBinding (e1, e2) ->
      let sub_rec = substitute_ext_env env in
      AppBinding (sub_rec e1, sub_rec e2)
  | _ -> e

(*
 * Get all of the objects except the initial or terminal object
 * Then get the assumption(s) and conclusion(s)
 * (This would be cleaner with a proper opposite category)
 *)
let partition_initial_terminal (c : proof_cat) (is_init : bool) =
  let i_t = map_if_else initial terminal is_init c in
  bind
    (bind (objects c) (all_objects_except i_t))
    (fun os ->
      bind
        (partition_state
           (branch_state (fun _ -> ret is_init) (maps_from i_t) (maps_to i_t))
           (morphisms c))
        (fun (c_or_a, as_or_cs)-> ret (os, List.hd c_or_a, as_or_cs)))

(* Substitute in an expanded version exp of the terminal object of c *)
let substitute_terminal (c : proof_cat) (exp : proof_cat) =
  bind
    (partition_initial_terminal c false)
    (fun (old_os, old_concl, old_assums) ->
      bind
        (partition_initial_terminal exp true)
        (fun (new_os, new_assum, new_concls) ->
          let os = List.append old_os new_os in
          let (s1, e1, _) = old_concl in
          let (_, e2, d2) = new_assum in
          let concls =
            if ext_is_lambda e1 then
              let (_, _, d3) = List.hd new_concls in
              let other_concls = List.tl new_concls in
              let e3 = curry_lambda e1 in
              (s1, e2, d2) :: ((d2, e3, d3) :: other_concls)
            else
              (s1, e2, d2) :: new_concls
          in
          let ms = List.append old_assums concls in
          make_category os ms (initial_opt c) (terminal_opt exp)))

(* --- Merging categories --- *)

(*
 * Substitute a source category into a destination category
 * That is, substitute the terminal object of sc for the initial object in dc
 * Assumes that sc has a terminal object and dc has an initial object
 * Creates fresh IDs for dc first to make sure we don't get repetition
 *)
let substitute_categories (sc : proof_cat) (dc : proof_cat) =
  bind
    (make_all_fresh dc)
    (fun dcf ->
      let t = terminal sc in
      let i = initial dcf in
      bind
        (combine (initial_opt sc) (terminal_opt dcf) sc dcf)
        (fun c ->
          bind
            (apply_functor
               ret
               (map_source_arrow
                  (branch_state (objects_equal i) (fun _ -> ret t) ret))
               c)
            (remove_object i)))

(*
 * Find all of the contexts in c where the shortest path is length i
 * Assumes c has an initial object
 *)
let contexts_at_index (c : proof_cat) (i : int) =
  let rec find_at ms o n =
    if n = 0 then
      ret [o]
    else
      bind
        (arrows_with_source o ms)
        (flat_map_state (map_dest (fun d -> find_at ms d (n - 1))))
  in find_at (morphisms c) (initial c) i

(*
 * Find the context in c where the shortest path is length i
 * Errors if more than one such context exists
 * Assumes c has an initial object
 *)
let context_at_index (c : proof_cat) (i : int) =
  bind
    (contexts_at_index c i)
    (fun ois ->
      assert ((List.length ois) = 1);
      ret (List.hd ois))

(*
 * Merge the first n contexts, and from there on out, include everything from both c1 and c2
 * Fails if n is 0
 * Assumes those first n contexts are linear
 * Assumes the first n contexts are equal
 * Assumes c1 and c2 both have initial contexs
 *)
let merge_first_n (n : int) (c1 : proof_cat) (c2 : proof_cat) sigma =
  assert (n > 0);
  let sigma, end1 = context_at_index c1 (n - 1) sigma in
  let sigma, end2 = context_at_index c2 (n - 1) sigma in
  let sigma, (os2, ms2) =
    bind
      (arrows_from c2 end2)
      (fun path2 ->
        bind
          (map_state
            (map_source_arrow
               (branch_state (objects_equal end2) (fun _ -> ret end1) ret))
            path2)
          (fun ms2 -> ret (conclusions path2, ms2)))
      sigma
  in
  let sigma, (os1, ms1) =
    bind
      (objects c1)
      (fun os1 -> ret (os1, morphisms c1))
      sigma
  in
  let os = List.append os1 os2 in
  let ms = List.append (morphisms c1) ms2 in
  make_category os ms (initial_opt c1) None sigma

(*
 * Assume the first n objects in c are equal, and merge
 * any objects at that index
 * Assume c has an initial object
 *)
let merge_up_to_index (n : int) (c : proof_cat) =
  if n <= 1 then
    ret c
  else
    let i = initial c in
    bind
      (bind
         (paths_from c i)
         (map_state
            (fun ms -> make_category (i :: conclusions ms) ms (Some i) None)))
      (fun cs -> fold_left_state (merge_first_n n) (List.hd cs) (List.tl cs))

(*
 * Merge the conclusions for a non-recursive inductive type
 *
 * This actually doesn't make sense when there are different numbers
 * of parameters for different constructors, unless we pick a standard
 * for how to adjust indexes in those cases.
 *
 * So revisit this later. So far we haven't needed it.
 *)
let merge_conclusions_nonrec (c : proof_cat) =
  bind
    (filter_state (map_dest (is_not_hypothesis c)) (morphisms c))
    (fun non_assums ->
      match conclusions non_assums with
      | h :: t ->
         let merge_h_t =
           branch_state (fun o -> contains_object o t) (fun _ -> ret h) ret
         in
         bind
           (bind (objects c) (all_objects_except_those_in t))
           (fun os ->
             bind
               (map_arrows (map_state (map_dest_arrow merge_h_t)) c)
               (fun ms -> make_category os ms (initial_opt c) (Some h)))
      | [] ->
         ret c)

(*
 * Merge an inductive type
 * If is_rec, just merge the parameters
 * Otherwise, merge the n parameters and also the conclusions
 *)
let merge_inductive (is_rec : bool) (n : int) (c : proof_cat) =
  bind
    (merge_up_to_index (n + 1) c)
    (fun merged_params_c ->
      if is_rec then
        ret merged_params_c
      else
        merge_conclusions_nonrec merged_params_c)

(* --- Binding --- *)

(*
 * Bind an arrow from src to dst of m in c with extension e of m
 * If an arrow with an anonymous binding exists, then bind that arrow
 * Otherwise, add the arrow if it doesn't exist
 *
 * TODO rename!
 *)
let bind (c : proof_cat) (m : arrow) : proof_cat =
  let (src, e, dst) = m in
  let t = if snd (is_terminal c src Evd.empty) then Some dst else terminal_opt c in
  let i = if snd (is_initial c dst Evd.empty) then Some src else initial_opt c in
  let _, c' =
    apply_functor
      (fun o -> ret o)
      (fun m' ->
        if snd (arrows_equal (src, AnonymousBinding, dst) m' Evd.empty) then
          ret m
        else
          ret m')
      c
      Evd.empty
  in map_if
    (fun c' -> snd (set_initial_terminal i t (snd (add_arrow m c' Evd.empty)) Evd.empty))
    (not (snd (category_contains_arrow m c' Evd.empty)))
    c'
   

(*
 * Build a function application for the last extension in c
 * The extension e holds the function before it is applied
 * Apply that to the n most recent local bindings
 *)
let bind_apply_function (e : extension) (n : int) (c : proof_cat) : proof_cat =
  let args = List.rev (List.map (fun i -> Index i) (from_one_to n)) in
  let binding = List.fold_left (fun b r -> AppBinding (b, r)) e args in
  snd
    (apply_functor
       (fun o -> ret o)
       (fun m ->
         ret
           (map_if
              (fun (src, _, dst) -> (src, binding, dst))
              (snd (maps_to (terminal c) m Evd.empty))
              m))
       c
       Evd.empty)

(* Bind an inductive argument arg to the end of c *)
let bind_inductive_arg (arg : types) (c : proof_cat) : proof_cat =
  let t = terminal c in
  let bound = ext_of_term (context_env t) arg in
  snd
    (apply_functor
       (fun o -> ret o)
       (fun m ->
         ret
           (map_if
              (map_ext_arrow (fun _ -> bound))
              (snd (maps_to t m Evd.empty))
              m))
       c
       Evd.empty)

(* Bind an array of inductive arguments args to each category in cs *)
let bind_inductive_args (args : types array) (cs : proof_cat array) : proof_cat array =
  Array.mapi
    (fun i arg ->
      let c = cs.(i) in
      let _, t_index = shortest_path_length c (terminal c) Evd.empty in
      bind_inductive_arg (shift_by (t_index - 1) arg) c)
    args

(*
 * Auxiliary function for binding properties and parameters
 * Get the arrow for binding an optional property
 *)
let bind_property_arrow (po : types option) (m : arrow) : arrow =
  let _, env = map_dest (fun o -> ret (context_env o)) m Evd.empty in
  map_ext_arrow (fun e -> Option.default e (Option.map (ext_of_term env) po)) m

(*
 * Auxiliary function for binding properties and parameters
 * Get the arrows for binding a list of parameters
 *)
let bind_param_arrows (ps : types list) (ms : arrow list) : arrow list =
  let _, envs = map_state (map_dest (fun o -> ret (context_env o))) ms Evd.empty in
  let envs = Array.of_list envs in
  let pes = Array.of_list (List.mapi (fun i p -> ext_of_term envs.(i) p) ps) in
  List.mapi
    (fun i m ->
      map_ext_arrow (fun e -> if i < Array.length pes then pes.(i) else e) m)
    ms

(*
 * Auxiliary function for binding properties and parameters
 * Substitute parameters into an object o at distance d from the initial object
 * Get d from a map of context indexes to distances for efficiency
 *)
let sub_params subs ds o =
  let ci = context_index o in
  let d = List.assoc ci ds in
  match o with
  | Context(Term(trm, env), _) ->
     let subs_shift = shift_substitutions_by_uncoditional d subs in
     let trm' = substitute_params subs_shift trm in
     let env' = substitute_env_params subs_shift env in
     Context(Term(trm', env'), ci)
  | _ -> o

(*
 * Auxiliary function for binding properties and parameters
 * Substitute a property into an object o at distance d from the initial object
 * Get d from a map of context indexes to distances for efficiency
 *
 * Once we fix the shift_ext_by bug, we can move subs out of this function.
 * Then we won't need p_index and p_binding in here.
 * Also, no idea why distances here are off one from ext version.
 *)
let sub_property ds pi pb o =
  let ci = context_index o in
  let d = List.assoc ci ds in
  let d_to_p = d - pi in
  match o with
  | Context(Term(trm, env), _ ) ->
     let p_shift = shift_ext_by d_to_p pb in
     let subs = build_substitution (ext_term p_shift) no_substitutions in
     let subs_shift = shift_from_substitutions_by (d_to_p - 1) subs in
     let trm' = substitute_params subs_shift trm in
     let env' = substitute_env_params subs_shift env in
     Context(Term(trm', env'), ci)
  | _ -> o

(*
 * Auxiliary function for binding properties and parameters
 * Substitute a property and parameters into an object o
 * at distance d from the initial object
 * Get d from a map of context indexes to distances for efficiency
 *)
let sub_obj_property_params pi pb subs ds o =
  sub_params subs ds (sub_property ds pi pb o)

(*
 * Auxiliary function for binding properties and parameters
 * Substitute parameters into an extension e at distance d from initial
 * Get d from a map of context indexes to distances for efficiency
 *
 * Can still make this more efficient, but not sure if it's worth it
 *)
 let sub_ext_params subs ds env i e =
    let d = List.assoc i ds in
    let subs_shift = shift_substitutions_by d subs in
    substitute_ext_params subs_shift e

(*
 * Auxiliary function for binding properties and parameters
 * Substitute a property and parameters into an arrow m at distance d
 * from initial. Get d from a map for efficiency.
 *
 * For now, we don't use sub_ext_property because it is broken and also
 * doesn't ever appear to be useful so far. This may mean missing
 * patches later on.
 *)
let sub_arr_property_params pi pb subs ds m =
  let (s, e, d) = m in
  let env = context_env d in
  let ci = context_index s in
  let e' = sub_ext_params subs ds env ci e in
  let sub = sub_obj_property_params pi pb subs ds in
  (sub s, e', sub d)

(*
 * Auxiliary function for binding properties and parameters
 * Substitute a property and parameters into an a category c.
 *)
let sub_property_params npms pms pb c : proof_cat =
  let _, os = objects c Evd.empty in
  let ds = List.map (fun o -> (context_index o, snd (shortest_path_length c o Evd.empty))) os in
  let pms_es = List.map (map_ext ext_term) pms in
  let pms_shift = List.mapi (fun j t -> shift_by_unconditional (- (npms - j)) t) pms_es in
  let pms_shift_rev = List.rev pms_shift in
  let pms_subs = build_n_substitutions npms pms_shift_rev no_substitutions in
  let pi = npms + 1 in
  let pms_subs_shift = unshift_from_substitutions_by pi pms_subs in
  snd
    (apply_functor
       (fun o -> ret (sub_obj_property_params pi pb pms_subs_shift ds o))
       (fun a -> ret (sub_arr_property_params pi pb pms_subs_shift ds a))
       c
       Evd.empty)

(*
 * Bind an inductive property p and parameters pms in c
 * c is a proof category for an inductive proof
 * npms is the total number of possible parameters
 *)
let bind_property_and_params (po : types option) (pms : types list) (npms : int) (c : proof_cat) : proof_cat =
  let ms = morphisms c in
  let p_unbound = List.find (fun m -> snd (maps_to (snd (context_at_index c (npms + 1) Evd.empty)) m Evd.empty)) ms in
  let po_shift = Option.map (shift_by npms) po in
  let p_bound = bind_property_arrow po_shift p_unbound in
  let (last_param, p_binding, _) = p_bound in
  let _, pms_unbound = arrows_between c (initial c) last_param Evd.empty in
  let pms_shift = List.mapi (fun i p -> shift_by_unconditional (npms - i - 1) p) pms in
  let pms_bound = bind_param_arrows pms_shift pms_unbound in
  let _, ms_old = all_arrows_except_those_in (p_unbound :: pms_unbound) ms Evd.empty in
  let ms' = List.append pms_bound (p_bound :: ms_old) in
  let _, c' = make_category (snd (objects c Evd.empty)) ms' (initial_opt c) (terminal_opt c) Evd.empty in
  sub_property_params npms pms_bound p_binding c'

