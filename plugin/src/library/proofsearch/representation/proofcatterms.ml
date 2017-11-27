(* Logic for proof categories that is specific to terms and types *)

open Term
open Environ
open Proofcat
open Names
open Debruijn
open Assumptions
open Substitution
open Utilities
open Collections
open Coqterms
open Printing

(* --- Construction --- *)

(* Get the extension for a trm in env *)
let rec ext_of_term (env : env) (trm : types) : extension =
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
let unique_common_subpath (paths : arrow list list) : arrow list =
  List.fold_left
    (fun l path ->
      match l with
      | [] -> path
      | _ -> List.filter (fun m -> contains_arrow m path) l)
    []
    paths

(*
 * From a proof category that represents an inductive proof, get
 * the inductive parameters and the inductive property
 *
 * Not sure about reversal
 *)
let params_and_prop (c : proof_cat) (npms : int) : arrow list * arrow =
  let i = initial c in
  let paths = paths_from c i in
  if List.length paths = 1 then
    let path = Array.of_list (List.hd paths) in
    let subpath = List.rev (List.map (Array.get path) (range 0 (npms + 1))) in
    (List.rev (List.tl subpath), List.hd subpath)
  else
    let common_subpaths = List.rev (unique_common_subpath paths) in
    (List.tl common_subpaths, List.hd common_subpaths)

(*
 * From a proof category that represents an inductive proof, get
 * the inductive parameters
 *)
let params (c : proof_cat) (npms : int) : arrow list =
  fst (params_and_prop c npms)

(*
 * From a proof category that represents an inductive proof,
 * get the inductive property
 *)
let prop (c : proof_cat) (npms : int) : arrow =
  snd (params_and_prop c npms)

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
let split (c : proof_cat) : proof_cat list =
  let i = initial c in
  List.map
    (fun ms ->
      let os = i :: (conclusions ms) in
      let (_, _, t) = List.nth ms (List.length ms - 1) in
      make_category os ms (Some i) (Some t))
    (paths_from c i)

(* --- Transformations on terms and environments --- *)

(*
 * Curry a lambda extension
 * Fail if it is not a lambda
 *)
let curry_lambda (e : extension) : extension =
  assert (ext_is_lambda e);
  let LazyBinding (trm, env) = e in
  let (n, t, b) = destLambda trm in
  ext_of_term (push_rel (n, None, t) env) b

(* --- Finding terms and environments --- *)

(* Check if c has an inductive hypothesis *)
let has_ihs (c : proof_cat) : bool =
  List.exists arrow_is_ih (morphisms c)

(* Find the inductive hypotheses in c *)
let find_ihs (c : proof_cat) : arrow list =
  List.filter arrow_is_ih (morphisms c)

(* Find the distance to the closest IH to m given a list of IHs *)
let closest_ih c (ihs : arrow list) (m : arrow) : context_object * int =
  let (s, _, _) = m in
  let ih_proxes =
    List.sort
      (fun (_, i1) (_, i2) -> compare i1 i2)
      (List.map
         (map_dest (fun d -> (d, List.length (arrows_between c d s))))
         ihs)
  in List.hd ih_proxes

(* Determine which arrow is closer to an IH *)
let closer_to_ih c (ihs : arrow list) (m1 : arrow) (m2 : arrow) : int =
  let (m1_ih_dst, m1_ih_prox) = closest_ih c ihs m1 in
  let (m2_ih_dst, m2_ih_prox) = closest_ih c ihs m2 in
  let ih_1_index = shortest_path_length c m1_ih_dst in
  let ih_2_index = shortest_path_length c m2_ih_dst in
  if m1_ih_prox = m2_ih_prox then
    compare ih_1_index ih_2_index (* start lower *)
  else
    compare m1_ih_prox m2_ih_prox (* start closer to IH *)

(*
 * Sort cs so that the base cases are first in the list
 *)
let base_cases_first (cs : proof_cat list) : proof_cat list =
  List.stable_sort
    (fun c1 c2 ->
      let c1_is_ind = has_ihs c1 in
      let c2_is_ind = has_ihs c2 in
      if c1_is_ind && not c2_is_ind then
        1
      else if not c2_is_ind && c1_is_ind then
        -1
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
let map_ids (f : int -> int) (c : proof_cat) : proof_cat =
  apply_functor
    (fun (Context (c, id)) ->
      Context (c, f id))
    (fun (Context (s, sid), e, Context (d, did)) ->
      (Context (s, f sid), e, Context (d, f did)))
    c

(* Get a map from context identifiers to fresh identifiers *)
let get_fresh_ids (c : proof_cat) : (int * int) list =
  List.map (fun (Context (_, id)) -> (id, (fid ()))) (objects c)

(*
 * Make fresh identifiers for every context in c
 *)
let make_all_fresh (c : proof_cat) : proof_cat =
  let fids = get_fresh_ids c in
  map_ids (fun id -> List.assoc id fids) c

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
let partition_initial_terminal (c : proof_cat) (is_initial : bool) : (context_object list) * arrow * (arrow list) =
  let i_or_t = map_if (always is_initial) initial terminal c in
  let os = all_objects_except i_or_t (objects c) in
  let maps = map_if (always is_initial) (maps_from i_or_t) (maps_to i_or_t) in
  let (c_or_a, as_or_cs) = List.partition maps (morphisms c) in
  (os, List.hd c_or_a, as_or_cs)

(* Substitute in an expanded version exp of the terminal object of c *)
let substitute_terminal (c : proof_cat) (exp : proof_cat) : proof_cat =
  let (old_os, old_concl, old_assums) = partition_initial_terminal c false in
  let (new_os, new_assum, new_concls) = partition_initial_terminal exp true in
  let os = List.append old_os new_os in
  let (s1, e1, _) = old_concl in
  let (_, e2, d2) = new_assum in
  let ms =
    if ext_is_lambda e1 then
      let (_, _, d3) = List.hd new_concls in
      let other_concls = List.tl new_concls in
      let e3 = curry_lambda e1 in
      List.append old_assums ((s1, e2, d2) :: ((d2, e3, d3) :: other_concls))
    else
      List.append old_assums ((s1, e2, d2) :: new_concls)
  in make_category os ms (initial_opt c) (terminal_opt exp)

(* --- Merging categories --- *)

(*
 * Substitute a source category into a destination category
 * That is, substitute the terminal object of sc for the initial object in dc
 * Assumes that sc has a terminal object and dc has an initial object
 * Creates fresh IDs for dc first to make sure we don't get repetition
 *)
let substitute_categories (sc : proof_cat) (dc : proof_cat) : proof_cat =
  let dcf = make_all_fresh dc in
  let t = terminal sc in
  let i = initial dcf in
  remove_object
    i
    (apply_functor
      id
      (fun (src, e, dst) -> (map_if (objects_equal i) (always t) id src, e, dst))
      (combine (initial_opt sc) (terminal_opt dcf) sc dcf))

(*
 * Find all of the contexts in c where the shortest path is length i
 * Assumes c has an initial object
 *)
let contexts_at_index (c : proof_cat) (i : int) : context_object list =
  let rec find_at ms o n =
    if n = 0 then
      [o]
    else
      let adj = arrows_with_source o ms in
      flat_map (map_dest (fun d -> find_at ms d (n - 1))) adj
  in find_at (morphisms c) (initial c) i

(*
 * Find the context in c where the shortest path is length i
 * Errors if more than one such context exists
 * Assumes c has an initial object
 *)
let context_at_index (c : proof_cat) (i : int) : context_object =
  let ois = contexts_at_index c i in
  assert ((List.length ois) = 1);
  List.hd ois

(*
 * Merge the first n contexts, and from there on out, include everything from both c1 and c2
 * Fails if n is 0
 * Assumes those first n contexts are linear
 * Assumes the first n contexts are equal
 * Assumes c1 and c2 both have initial contexs
 *)
let merge_first_n (n : int) (c1 : proof_cat) (c2 : proof_cat) : proof_cat =
  assert (n > 0);
  let end1 = context_at_index c1 (n - 1) in
  let end2 = context_at_index c2 (n - 1) in
  let path2 = arrows_from c2 end2 in
  let os2 = conclusions path2 in
  let ms2 = List.map (map_source_arrow (map_if (objects_equal end2) (always end1) id)) path2 in
  let os = List.append (objects c1) os2 in
  let ms = List.append (morphisms c1) ms2 in
  make_category os ms (initial_opt c1) None

(*
 * Assume the first n objects in c are equal, and merge
 * any objects at that index
 * Assume c has an initial object
 *)
let merge_up_to_index (n : int) (c : proof_cat) : proof_cat =
  if n <= 1 then
    c
  else
    let i = initial c in
    let ps = paths_from c i in
    let cs = List.map (fun ms -> make_category (i :: conclusions ms) ms (Some i) None) ps in
    List.fold_left (merge_first_n n) (List.hd cs) (List.tl cs)

(*
 * Merge the conclusions for a non-recursive inductive type
 *
 * This actually doesn't make sense when there are different numbers
 * of parameters for different constructors, unless we pick a standard
 * for how to adjust indexes in those cases.
 *
 * So revisit this later. So far we haven't needed it.
 *)
let merge_conclusions_nonrec (c : proof_cat) : proof_cat =
  let non_assums = List.filter (map_dest (is_not_hypothesis c)) (morphisms c) in
  match conclusions non_assums with
  | h :: t ->
     let os = all_objects_except_those_in t (objects c) in
     let merge_h_t = map_if (fun o -> contains_object o t) (always h) id in
     let ms = map_arrows (List.map (map_dest_arrow merge_h_t)) c in
     make_category os ms (initial_opt c) (Some h)
  | [] -> c

(*
 * Merge an inductive type
 * If is_rec, just merge the parameters
 * Otherwise, merge the n parameters and also the conclusions
 *)
let merge_inductive (is_rec : bool) (n : int) (c : proof_cat) : proof_cat =
  let merged_params_c = merge_up_to_index (n + 1) c in
  if is_rec then
    merged_params_c
  else
    merge_conclusions_nonrec merged_params_c

(* --- Binding --- *)

(*
 * Bind an arrow from src to dst of m in c with extension e of m
 * If an arrow with an anonymous binding exists, then bind that arrow
 * Otherwise, add the arrow if it doesn't exist
 *)
let bind (c : proof_cat) (m : arrow) : proof_cat =
  let (src, e, dst) = m in
  let t = map_if (is_terminal c) (always (Some dst)) (always (terminal_opt c)) src in
  let i = map_if (is_initial c) (always (Some src)) (always (initial_opt c)) dst in
  map_if
    (category_contains_arrow m)
    id
    (fun c' -> set_initial_terminal i t (add_arrow m c'))
    (apply_functor
      id
      (map_if
         (arrows_equal (src, AnonymousBinding, dst))
         (always m)
         id)
      c)

(*
 * Build a function application for the last extension in c
 * The extension e holds the function before it is applied
 * Apply that to the n most recent local bindings
 *)
let bind_apply_function (e : extension) (n : int) (c : proof_cat) : proof_cat =
  let args = List.rev (List.map (fun i -> Index i) (from_one_to n)) in
  let binding = List.fold_left (fun b r -> AppBinding (b, r)) e args in
  apply_functor
    id
    (map_if
      (maps_to (terminal c))
      (fun (src, _, dst) -> (src, binding, dst))
      id)
    c

(* Bind an inductive argument arg to the end of c *)
let bind_inductive_arg (arg : types) (c : proof_cat) : proof_cat =
  let t = terminal c in
  let bound = ext_of_term (context_env t) arg in
  apply_functor
    id
    (map_if
       (maps_to t)
       (map_ext_arrow (always bound))
       id)
    c

(* Bind an array of inductive arguments args to each category in cs *)
let bind_inductive_args (args : types array) (cs : proof_cat array) : proof_cat array =
  Array.mapi
    (fun i arg ->
      let c = cs.(i) in
      let t_index = shortest_path_length c (terminal c) in
      bind_inductive_arg (shift_by (t_index - 1) arg) c)
    args

(*
 * Auxiliary function for binding properties and parameters
 * Get the arrow for binding an optional property
 *)
let bind_property_arrow (po : types option) (m : arrow) : arrow =
  let env = map_dest context_env m in
  map_ext_arrow (fun e -> Option.default e (Option.map (ext_of_term env) po)) m

(*
 * Auxiliary function for binding properties and parameters
 * Get the arrows for binding a list of parameters
 *)
let bind_param_arrows (ps : types list) (ms : arrow list) : arrow list =
  let envs = Array.of_list (List.map (map_dest context_env) ms) in
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
 * Substitute a property into an extension e at distance d from initial
 * Get d from a map of context indexes to distances for efficiency
 *
 * Can still make this more efficient, but not sure if it's worth it
 *)
 let sub_ext_property ds pi pb env i e =
   let d = List.assoc i ds in
   let d_to_p = d - pi in
   let p_shift = shift_ext_by d_to_p pb in
   let subs = build_substitution (ext_term p_shift) no_substitutions in
   let subs_shift = shift_from_substitutions_by d_to_p subs in
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
  let os = objects c in
  let ds = List.map (fun o -> (context_index o, shortest_path_length c o)) os in
  let pms_es = List.map (map_ext ext_term) pms in
  let pms_shift = List.mapi (fun j t -> shift_by_unconditional (- (npms - j)) t) pms_es in
  let pms_shift_rev = List.rev pms_shift in
  let pms_subs = build_n_substitutions npms pms_shift_rev no_substitutions in
  let pi = npms + 1 in
  let pms_subs_shift = unshift_from_substitutions_by pi pms_subs in
  apply_functor
    (sub_obj_property_params pi pb pms_subs_shift ds)
    (sub_arr_property_params pi pb pms_subs_shift ds)
    c

(*
 * Bind an inductive property p and parameters pms in c
 * c is a proof category for an inductive proof
 * npms is the total number of possible parameters
 *)
let bind_property_and_params (po : types option) (pms : types list) (npms : int) (c : proof_cat) : proof_cat =
  let ms = morphisms c in
  let p_unbound = List.find (maps_to (context_at_index c (npms + 1))) ms in
  let po_shift = Option.map (shift_by npms) po in
  let p_bound = bind_property_arrow po_shift p_unbound in
  let (last_param, p_binding, _) = p_bound in
  let pms_unbound = arrows_between c (initial c) last_param in
  let pms_shift = List.mapi (fun i p -> shift_by_unconditional (npms - i - 1) p) pms in
  let pms_bound = bind_param_arrows pms_shift pms_unbound in
  let ms_old = all_arrows_except_those_in (p_unbound :: pms_unbound) ms in
  let ms' = List.append pms_bound (p_bound :: ms_old) in
  let c' = make_category (objects c) ms' (initial_opt c) (terminal_opt c) in
  sub_property_params npms pms_bound p_binding c'

