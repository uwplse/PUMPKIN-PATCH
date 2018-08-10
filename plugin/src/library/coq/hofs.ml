(* Higher-order functions on terms *)

(* TODO maps should handle other types, right now don't yet *)
(* TODO can still generalize these to make them easier to extend further *)

open Environ
open Constr
open Coqterms
open Coqenvs
open Collections
open Names

module CRD = Context.Rel.Declaration

(* Predicates to determine whether to apply a mapped function *)
type ('a, 'b) pred = 'a -> 'b -> bool
type ('a, 'b) pred_with_env = env -> ('a, 'b) pred

(* Functions to use in maps *)
type ('a, 'b) transformer = 'a -> 'b -> 'b
type ('a, 'b) cartesian_transformer = 'a -> 'b -> 'b list
type ('a, 'b) transformer_with_env = env -> 'a -> 'b -> 'b
type ('a, 'b) cartesian_transformer_with_env = env -> 'a -> 'b -> 'b list

(* Updating arguments *)
type 'a updater = 'a -> 'a

(* Mapper functions *)
type ('a, 'b) mapper_with_env =
  ('a, 'b) transformer_with_env ->
  'a updater ->
  ('a, 'b) transformer_with_env

type ('a, 'b) mapper =
  ('a, 'b) transformer ->
  'a updater ->
  ('a, 'b) transformer

type ('a, 'b) cartesian_mapper_with_env =
  ('a, 'b) cartesian_transformer_with_env ->
  'a updater ->
  ('a, 'b) cartesian_transformer_with_env

type ('a, 'b) cartesian_mapper =
  ('a, 'b) cartesian_transformer ->
  'a updater ->
  ('a, 'b) cartesian_transformer

type ('a, 'b) conditional_mapper_with_env =
  ('a, 'b) pred_with_env ->
  ('a, 'b) transformer_with_env ->
  'a updater ->
  ('a, 'b) transformer_with_env

type ('a, 'b) conditional_mapper =
  ('a, 'b) pred ->
  ('a, 'b) transformer ->
  'a updater ->
  ('a, 'b) transformer

type ('a, 'b) conditional_cartesian_mapper_with_env =
  ('a, 'b) pred_with_env ->
  ('a, 'b) cartesian_transformer_with_env ->
  'a updater ->
  ('a, 'b) cartesian_transformer_with_env

(* Specific predicates and functions for implementation *)
type 'a p_no_env = ('a, types) pred
type 'a p_with_env = ('a, types) pred_with_env
type 'a pe_with_env = ('a, eterm) pred_with_env
type 'a f_no_env = ('a, types) transformer
type 'a fe_no_env = ('a, eterm) transformer
type 'a f_with_env = ('a, types) transformer_with_env
type 'a fe_with_env = ('a, eterm) transformer_with_env
type 'a f_cart_with_env = ('a, types) cartesian_transformer_with_env
type 'a f_cart_no_env = ('a, types) cartesian_transformer

(* --- Terms --- *)

(*
 * Recurse on a mapping function with an environment for a fixpoint
 *)
let map_rec_env_fix (map_rec : ('a, 'b) transformer_with_env) (d : 'a updater) (env : env) (a : 'a) (ns : Name.t array) (ts : types array) =
  let fix_bindings = bindings_for_fix ns ts in
  let env_fix = push_rel_context fix_bindings env in
  let n = List.length fix_bindings in
  let d_n = List.fold_left (fun a' _ -> d a') a (range 0 n) in
  map_rec env_fix d_n

(*
 * Recurse on a mapping function with an environment for a fixpoint
 *)
let map_rec_env_fix_cartesian (map_rec : ('a, 'b) cartesian_transformer_with_env) (d : 'a updater) (env : env) (a : 'a) (ns : Name.t array) (ts : types array) =
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
let rec map_term_env (f : 'a f_with_env) (d : 'a updater) (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env f d in
  match kind trm with
  | Cast (c, k, t) ->
     let c' = map_rec env a c in
     let t' = map_rec env a t in
     mkCast (c', k, t')
  | Prod (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
     mkProd (n, t', b')
  | Lambda (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
     mkLambda (n, t', b')
  | LetIn (n, trm, typ, e) ->
     let trm' = map_rec env a trm in
     let typ' = map_rec env a typ in
     let e' = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) e in
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
let map_term (f : 'a f_no_env) (d : 'a updater) (a : 'a) (trm : types) : types =
  map_term_env (fun _ a t -> f a t) d empty_env a trm

(*
 * Map a function over subterms of a term in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
let rec map_subterms_env (f : 'a f_cart_with_env) (d : 'a updater) (env : env) (a : 'a) (trm : types) : types list =
  let map_rec = map_subterms_env f d in
  match kind trm with
  | Cast (c, k, t) ->
     let cs' = map_rec env a c in
     let ts' = map_rec env a t in
     combine_cartesian (fun c' t' -> mkCast (c', k, t')) cs' ts'
  | Prod (n, t, b) ->
     let ts' = map_rec env a t in
     let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
     combine_cartesian (fun t' b' -> mkProd (n, t', b')) ts' bs'
  | Lambda (n, t, b) ->
     let ts' = map_rec env a t in
     let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
     combine_cartesian (fun t' b' -> mkLambda (n, t', b')) ts' bs'
  | LetIn (n, trm, typ, e) ->
     let trms' = map_rec env a trm in
     let typs' = map_rec env a typ in
     let es' = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) e in
     combine_cartesian (fun trm' (typ', e') -> mkLetIn (n, trm', typ', e')) trms' (cartesian typs' es')
  | App (fu, args) ->
     let fus' = map_rec env a fu in
     let argss' = combine_cartesian_append (Array.map (map_rec env a) args) in
     combine_cartesian (fun fu' args' -> mkApp (fu', args')) fus' argss'
  | Case (ci, ct, m, bs) ->
     let cts' = map_rec env a ct in
     let ms' = map_rec env a m in
     let bss' = combine_cartesian_append (Array.map (map_rec env a) bs) in
     combine_cartesian (fun ct' (m', bs') -> mkCase (ci, ct', m', bs')) cts' (cartesian ms' bss')
  | Fix ((is, i), (ns, ts, ds)) ->
     let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
     let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
     combine_cartesian (fun ts' ds' -> mkFix ((is, i), (ns, ts', ds'))) tss' dss'
  | CoFix (i, (ns, ts, ds)) ->
     let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
     let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
     combine_cartesian (fun ts' ds' -> mkCoFix (i, (ns, ts', ds'))) tss' dss'
  | Proj (p, c) ->
     let cs' = map_rec env a c in
     List.map (fun c' -> mkProj (p, c')) cs'
  | _ ->
     f env a trm

(*
 * Map a function over subterms of a term, when the environment doesn't matter
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
let map_subterms (f : 'a f_cart_no_env) (d : 'a updater) (a : 'a) (trm : types) : types list =
  map_subterms_env (fun _ a t -> f a t) d empty_env a trm

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let rec map_term_env_if (p : 'a p_with_env) (f : 'a f_with_env) (d : 'a updater) (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if p f d in
  if p env a trm then
    f env a trm
  else
    match kind trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_rel CRD.(LocalDef(n, e, typ')) env) (d a) e in
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
    | Proj (pr, c) ->
       let c' = map_rec env a c in
       mkProj (pr, c')
    | _ ->
       trm

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Don't recurse into lambda arguments
 * Return a new term
 *)
let rec map_term_env_if_shallow (p : 'a p_with_env) (f : 'a f_with_env) (d : 'a updater) (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if_shallow p f d in
  if p env a trm then
    f env a trm
  else
    match kind trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_rel CRD.(LocalDef(n, e, typ')) env) (d a) e in
       mkLetIn (n, trm', typ', e')
    | App (fu, args) ->
       let fu' = map_rec env a fu in
       let args' =
         Array.map
           (fun t -> if isLambda t then t else map_rec env a t)
           args
       in mkApp (fu', args')
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
    | Proj (pr, c) ->
       let c' = map_rec env a c in
       mkProj (pr, c')
    | _ ->
       trm


(*
 * Map a function over a term where the environment doesn't matter
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let map_term_if (p : 'a p_no_env) (f : 'a f_no_env) (d : 'a updater) (a : 'a) (trm : types) : types =
  map_term_env_if (fun _ a t -> p a t) (fun _ a t -> f a t) d empty_env a trm

(*
 * Map a function over subterms of a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
let rec map_subterms_env_if (p : 'a p_with_env) (f : 'a f_cart_with_env) (d : 'a updater) (env : env) (a : 'a) (trm : types) : types list =
  let map_rec = map_subterms_env_if p f d in
  if p env a trm then
    f env a trm
  else
    match kind trm with
    | Cast (c, k, t) ->
       let cs' = map_rec env a c in
       let ts' = map_rec env a t in
       combine_cartesian (fun c' t' -> mkCast (c', k, t')) cs' ts'
    | Prod (n, t, b) ->
       let ts' = map_rec env a t in
       let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
       combine_cartesian (fun t' b' -> mkProd (n, t', b')) ts' bs'
    | Lambda (n, t, b) ->
       let ts' = map_rec env a t in
       let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
       combine_cartesian (fun t' b' -> mkLambda (n, t', b')) ts' bs'
    | LetIn (n, trm, typ, e) ->
       let trms' = map_rec env a trm in
       let typs' = map_rec env a typ in
       let es' = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) e in
       combine_cartesian (fun trm' (typ', e') -> mkLetIn (n, trm', typ', e')) trms' (cartesian typs' es')
    | App (fu, args) ->
       let fus' = map_rec env a fu in
       let argss' = combine_cartesian_append (Array.map (map_rec env a) args) in
       combine_cartesian (fun fu' args' -> mkApp (fu', args')) fus' argss'
    | Case (ci, ct, m, bs) ->
       let cts' = map_rec env a ct in
       let ms' = map_rec env a m in
       let bss' = combine_cartesian_append (Array.map (map_rec env a) bs) in
       combine_cartesian (fun ct' (m', bs') -> mkCase (ci, ct', m', bs')) cts' (cartesian ms' bss')
    | Fix ((is, i), (ns, ts, ds)) ->
       let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
       let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
       combine_cartesian (fun ts' ds' -> mkFix ((is, i), (ns, ts', ds'))) tss' dss'
    | CoFix (i, (ns, ts, ds)) ->
       let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
       let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
       combine_cartesian (fun ts' ds' -> mkCoFix (i, (ns, ts', ds'))) tss' dss'
    | Proj (p, c) ->
       let cs' = map_rec env a c in
       List.map (fun c' -> mkProj (p, c')) cs'
    | _ ->
       [trm]

(*
 * Map a function over subterms of a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly, but always recurse
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *)
let rec map_subterms_env_if_combs (p : 'a p_with_env) (f : 'a f_cart_with_env) (d : 'a updater) (env : env) (a : 'a) (trm : types) : types list =
  let map_rec = map_subterms_env_if_combs p f d in
  let trms = if p env a trm then f env a trm else [trm] in
  flat_map
    (fun trm' ->
      match kind trm' with
      | Cast (c, k, t) ->
         let cs' = map_rec env a c in
         let ts' = map_rec env a t in
         combine_cartesian (fun c' t' -> mkCast (c', k, t')) cs' ts'
      | Prod (n, t, b) ->
         let ts' = map_rec env a t in
         let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
         combine_cartesian (fun t' b' -> mkProd (n, t', b')) ts' bs'
      | Lambda (n, t, b) ->
         let ts' = map_rec env a t in
         let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
         combine_cartesian (fun t' b' -> mkLambda (n, t', b')) ts' bs'
      | LetIn (n, trm, typ, e) ->
         let trms' = map_rec env a trm in
         let typs' = map_rec env a typ in
         let es' = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) e in
         combine_cartesian (fun trm' (typ', e') -> mkLetIn (n, trm', typ', e')) trms' (cartesian typs' es')
      | App (fu, args) ->
         let fus' = map_rec env a fu in
         let argss' = combine_cartesian_append (Array.map (map_rec env a) args) in
         combine_cartesian (fun fu' args' -> mkApp (fu', args')) fus' argss'
      | Case (ci, ct, m, bs) ->
         let cts' = map_rec env a ct in
         let ms' = map_rec env a m in
         let bss' = combine_cartesian_append (Array.map (map_rec env a) bs) in
         combine_cartesian (fun ct' (m', bs') -> mkCase (ci, ct', m', bs')) cts' (cartesian ms' bss')
      | Fix ((is, i), (ns, ts, ds)) ->
         let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
         let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
         combine_cartesian (fun ts' ds' -> mkFix ((is, i), (ns, ts', ds'))) tss' dss'
      | CoFix (i, (ns, ts, ds)) ->
         let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
         let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
         combine_cartesian (fun ts' ds' -> mkCoFix (i, (ns, ts', ds'))) tss' dss'
      | Proj (p, c) ->
         let cs' = map_rec env a c in
         List.map (fun c' -> mkProj (p, c')) cs'
      | _ ->
         [trm'])
    trms

(*
 * Map a function over subterms of a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function after recursing
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return all combinations of new terms
 *
 * TODO redundant calls right now
 *)
let rec map_subterms_env_if_lazy (p : 'a p_with_env) (f : 'a f_cart_with_env) (d : 'a updater) (env : env) (a : 'a) (trm : types) : types list =
  let map_rec = map_subterms_env_if_lazy p f d in
  let trms' =
    match kind trm with
    | Cast (c, k, t) ->
       let cs' = map_rec env a c in
       let ts' = map_rec env a t in
       combine_cartesian (fun c' t' -> mkCast (c', k, t')) cs' ts'
    | Prod (n, t, b) ->
       let ts' = map_rec env a t in
       let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
       combine_cartesian (fun t' b' -> mkProd (n, t', b')) ts' bs'
    | Lambda (n, t, b) ->
       let ts' = map_rec env a t in
       let bs' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
       combine_cartesian (fun t' b' -> mkLambda (n, t', b')) ts' bs'
    | LetIn (n, trm, typ, e) ->
       let trms' = map_rec env a trm in
       let typs' = map_rec env a typ in
       let es' = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) e in
       combine_cartesian (fun trm' (typ', e') -> mkLetIn (n, trm', typ', e')) trms' (cartesian typs' es')
    | App (fu, args) ->
       let fus' = map_rec env a fu in
       let argss' = combine_cartesian_append (Array.map (map_rec env a) args) in
       combine_cartesian (fun fu' args' -> mkApp (fu', args')) fus' argss'
    | Case (ci, ct, m, bs) ->
       let cts' = map_rec env a ct in
       let ms' = map_rec env a m in
       let bss' = combine_cartesian_append (Array.map (map_rec env a) bs) in
       combine_cartesian (fun ct' (m', bs') -> mkCase (ci, ct', m', bs')) cts' (cartesian ms' bss')
    | Fix ((is, i), (ns, ts, ds)) ->
       let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
       let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
       combine_cartesian (fun ts' ds' -> mkFix ((is, i), (ns, ts', ds'))) tss' dss'
    | CoFix (i, (ns, ts, ds)) ->
       let tss' = combine_cartesian_append (Array.map (map_rec env a) ts) in
       let dss' = combine_cartesian_append (Array.map (map_rec_env_fix_cartesian map_rec d env a ns ts) ds) in
       combine_cartesian (fun ts' ds' -> mkCoFix (i, (ns, ts', ds'))) tss' dss'
    | Proj (p, c) ->
       let cs' = map_rec env a c in
       List.map (fun c' -> mkProj (p, c')) cs'
    | _ ->
       [trm]
  in flat_map (fun trm' -> if p env a trm' then f env a trm' else [trm']) trms'

(* --- Terms with existential variables --- *)

(* Map over terms with existential variables *)
let map_eterms (f : eterm -> eterm) ((evm, ts) : eterms) : eterms =
  let (evm', ts') =
    Array.fold_right
      (fun t (evm, l) ->
        let (evm', t') = f (evm, t) in
        (evm', t' :: l))
      ts
      (evm, [])
  in (evm', Array.of_list ts')

(*
 * Map a function over an eterm in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new eterm
 *)
let rec map_eterm_env (f : 'a fe_with_env) (d : 'a updater) (env : env) (a : 'a) ((evm, trm) : eterm) : eterm =
  let map_rec = map_eterm_env f d in
  match kind trm with
  | Cast (c, k, t) ->
     let (evm', c') = map_rec env a (evm, c) in
     let (evm'', t') = map_rec env a (evm', t) in
     (evm'', mkCast (c', k, t'))
  | Prod (n, t, b) ->
     let (evm', t') = map_rec env a (evm, t) in
     let (evm'', b') = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) (evm', b) in
     (evm'', mkProd (n, t', b'))
  | Lambda (n, t, b) ->
     let (evm', t') = map_rec env a (evm, t) in
     let (evm'', b') = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) (evm', b) in
     (evm'', mkLambda (n, t', b'))
  | LetIn (n, trm, typ, e) ->
     let (evm', trm') = map_rec env a (evm, trm) in
     let (evm'', typ') = map_rec env a (evm', typ) in
     let (evm''', e') = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) (evm'', e) in
     (evm''', mkLetIn (n, trm', typ', e'))
  | App (fu, args) ->
     let (evm', fu') = map_rec env a (evm, fu) in
     let (evm'', args') = map_eterms (map_rec env a) (evm', args) in
     (evm'', mkApp (fu', args'))
  | Case (ci, ct, m, bs) ->
     let (evm', ct') = map_rec env a (evm, ct) in
     let (evm'', m') = map_rec env a (evm', m) in
     let (evm''', bs') = map_eterms (map_rec env a) (evm'', bs) in
     (evm''', mkCase (ci, ct', m', bs'))
  | Fix ((is, i), (ns, ts, ds)) ->
     let (evm', ts') = map_eterms (map_rec env a) (evm, ts) in
     let (evm'', ds') = map_eterms (map_rec_env_fix map_rec d env a ns ts) (evm', ds) in
     (evm'', mkFix ((is, i), (ns, ts', ds')))
  | CoFix (i, (ns, ts, ds)) ->
     let (evm', ts') = map_eterms (map_rec env a) (evm, ts) in
     let (evm'', ds') = map_eterms (map_rec_env_fix map_rec d env a ns ts) (evm', ds) in
     (evm'', mkCoFix (i, (ns, ts', ds')))
  | Proj (p, c) ->
     let (evm', c') = map_rec env a (evm, c) in
     (evm', mkProj (p, c'))
  | _ ->
     f env a (evm, trm)

(*
 * Map a function over an eterm in where the environment doesn't matter
 * Update the argument of type 'a using the a supplied update function
 * Return a new eterm
 *)
let map_eterm (f : 'a fe_no_env) (d : 'a updater) (a : 'a) (etrm : eterm) : eterm =
  map_eterm_env (fun _ a t -> f a t) d empty_env a etrm

(*
 * Map a function over an term in an environment
 * Only apply the function when a proposition is true
 * Apply the function lazily, to the result
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new eterm
 *)
let rec map_eterm_env_if_lazy (p : 'a pe_with_env) (f : 'a fe_with_env) (d : 'a updater) (env : env) (a : 'a) ((evm, trm) : eterm) : eterm =
  let map_rec = map_eterm_env_if_lazy p f d in
  let (evm', trm') =
    match kind trm with
    | Cast (c, k, t) ->
       let (evm', c') = map_rec env a (evm, c) in
       let (evm'', t') = map_rec env a (evm', t) in
       (evm'', mkCast (c', k, t'))
    | Prod (n, t, b) ->
       let (evm', t') = map_rec env a (evm, t) in
       let (evm'', b') = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) (evm', b) in
       (evm'', mkProd (n, t', b'))
    | Lambda (n, t, b) ->
       let (evm', t') = map_rec env a (evm, t) in
       let (evm'', b') = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) (evm', b) in
       (evm'', mkLambda (n, t', b'))
    | LetIn (n, trm, typ, e) ->
       let (evm', trm') = map_rec env a (evm, trm) in
       let (evm'', typ') = map_rec env a (evm', typ) in
       let (evm''', e') = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) (evm'', e) in
       (evm''', mkLetIn (n, trm', typ', e'))
    | App (fu, args) ->
       let (evm', fu') = map_rec env a (evm, fu) in
       let (evm'', args') = map_eterms (map_rec env a) (evm', args) in
       (evm'', mkApp (fu', args'))
    | Case (ci, ct, m, bs) ->
       let (evm', ct') = map_rec env a (evm, ct) in
       let (evm'', m') = map_rec env a (evm', m) in
       let (evm''', bs') = map_eterms (map_rec env a) (evm'', bs) in
       (evm''', mkCase (ci, ct', m', bs'))
    | Fix ((is, i), (ns, ts, ds)) ->
       let (evm', ts') = map_eterms (map_rec env a) (evm, ts) in
       let (evm'', ds') = map_eterms (map_rec_env_fix map_rec d env a ns ts) (evm', ds) in
       (evm'', mkFix ((is, i), (ns, ts', ds')))
    | CoFix (i, (ns, ts, ds)) ->
       let (evm', ts') = map_eterms (map_rec env a) (evm, ts) in
       let (evm'', ds') = map_eterms (map_rec_env_fix map_rec d env a ns ts)(evm', ds) in
       (evm'', mkCoFix (i, (ns, ts', ds')))
    | Proj (p, c) ->
       let (evm', c') = map_rec env a (evm, c) in
       (evm', mkProj (p, c'))
    | _ ->
       (evm, trm)
  in
  if p env a (evm', trm') then
    f env a (evm', trm')
  else
    (evm', trm')
