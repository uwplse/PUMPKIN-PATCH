(* Proof categories, core logic *)

open Category
open Constr
open Environ
open Evd
open Printing
open Assumptions
open Utilities
open Merging
open Stateutils

(*
 * Note: We will soon get rid of this representation.
 * It is inefficient and makes the code more difficult to understand.
 *)

(* --- TODO for refactor: Use this order in lib later --- *)

let convertible env t1 t2 sigma =
  Convertibility.convertible env sigma t1 t2

let types_convertible env t1 t2 sigma =
  Convertibility.types_convertible env sigma t1 t2

(* --- End TODO *)
  
       
(* --- Type definitions --- *)

(* TODO don't need envs in extensions when we have bindings [except for printing right now] *)
(* TODO can clean up more once envs are gone *)
(* TODO removing index from extension and trying to fix back to rel always breaks things for some reason *)
(* TODO when we remove extra envs, note that initial context should have env *)

(* Types of objects and arrows *)
type type_context = Term of types * env | Gamma
type context_object = Context of type_context * int
type extension = AnonymousBinding | InductiveHypothesis of int | Index of int | LazyBinding of types * env | AppBinding of extension * extension

(* Initial context *)
let initial_context = Context (Gamma, 0)

(* Modules for objects and arrows *)
module TypeContext  =
struct
  type t = context_object

  (* Prints a context node *)
  let ctx_as_string (c : type_context) =
    match c with
    | Term (trm, env) -> term_as_string env trm
    | Gamma -> "Γ"

  let as_string (c : t) =
    match c with
    | Context (ctx, i) ->
       Printf.sprintf "%s [%s]" (ctx_as_string ctx) (string_of_int i)

  (* For now we just trust IDs, later if we want we can change this *)
  let ctx_equal (ctx1 : type_context) (ctx2 : type_context) =
    true

  let equal (c1 : t) (c2 : t) =
    ret
      (let Context (ctx1, i1) = c1 in
       let Context (ctx2, i2) = c2 in
       (i1 = i2) && (ctx_equal ctx1 ctx2))
end

module Extension =
struct
  type t = extension

 (* Prints an extension edge *)
  let rec as_string (e : t) =
    match e with
    | AnonymousBinding ->
       "Anonymous"
    | Index i ->
       Printf.sprintf "(Rel %d)" i
    | InductiveHypothesis i ->
       Printf.sprintf "(IH %d)" i
    | LazyBinding (trm, env) ->
       term_as_string env trm
    | AppBinding (e1, e2) ->
       Printf.sprintf "(%s %s)" (as_string e1) (as_string e2)

  let rec equal e1 e2 =
    match (e1, e2) with
    | (LazyBinding (trm1, env1), LazyBinding (trm2, env2)) ->
       if env1 == env2 then
         convertible env1 trm1 trm2
       else
         let (env, trm1s, trm2s) = merge_closures (env1, [trm1]) (env2, [trm2]) no_assumptions in
         convertible env (List.hd trm1s) (List.hd trm2s)
    | (AppBinding (e11, e21), AppBinding (e12, e22)) ->
       and_state (equal e11) (equal e21) e12 e22 (* imperfect *)
    | _ ->
       ret (e1 = e2)
end

(* Categories *)
module ProofCat = Category (TypeContext) (Extension)
type proof_cat = ProofCat.cat
type arrow = ProofCat.arrow

(* Initial category *)
let initial_category : evar_map -> proof_cat state =
  ProofCat.make [initial_context] [] (Some initial_context) None

(* Initial and terminal objects *)
type initial_object = context_object option
type terminal_object = context_object option

(* --- Printing --- *)

let context_as_string = TypeContext.as_string
let extension_as_string = Extension.as_string
let proof_as_string = ProofCat.as_string

(* --- Objects, extensions, and arrows --- *)

let objects = ProofCat.objects
let morphisms = ProofCat.morphisms

(*
 * True iff o1 and o2 are equal
 *)
let objects_equal (o1 : context_object) (o2 : context_object) =
  TypeContext.equal o1 o2

(*
 * True iff o1 and o2 are not equal
 *)
let objects_not_equal (o1 : context_object) (o2 : context_object) =
  not_state (objects_equal o1) o2

(*
 * True iff os contains o
 *)
let contains_object (o : context_object) (os : context_object list) =
  exists_state (objects_equal o) os

(*
 * True iff os doesn't contain o
 *)
let not_contains_object (o : context_object) (os : context_object list) =
  not_state (contains_object o) os

(*
 * True iff e1 and e2 are equal
 *)
let extensions_equal (e1 : extension) (e2 : extension) =
  Extension.equal e1 e2

(*
 * True iff e1 and e2 are not equal
 *)
let extensions_not_equal (e1 : extension) (e2 : extension) =
  not_state (extensions_equal e1) e2

(* Check if two extensions are equal with a set of assumptions *)
let rec extensions_equal_assums assums (e1 : extension) (e2 : extension) =
  match (e1, e2) with
  | (LazyBinding(trm1, env1), LazyBinding(trm2, env2)) ->
     if env1 == env2 then
       convertible env1 trm1 trm2
     else
       let (env, trm1s, trm2s) = merge_closures (env1, [trm1]) (env2, [trm2]) assums in
       convertible env (List.hd trm1s) (List.hd trm2s)
  | (AppBinding (e11, e21), AppBinding (e12, e22)) ->
     and_state (extensions_equal_assums assums e11) (extensions_equal_assums assums e21) e12 e22 (* imperfect *)
  | _ ->
     ret (e1 = e2)

(*
 * True iff a1 and a2 are equal
 *)
let arrows_equal (m1 : arrow) (m2 : arrow) =
  let (src1, e1, dst1) = m1 in
  let (src2, e2, dst2) = m2 in
  and_state
    (objects_equal src1)
    (and_state (extensions_equal e1) (objects_equal dst1) e2)
    src2
    dst2

(*
 * True iff a1 and a2 are not equal
 *)
let arrows_not_equal (m1 : arrow) (m2 : arrow) =
  not_state (arrows_equal m1) m2

(*
 * True iff ms contains m
 *)
let contains_arrow (m : arrow) (ms : arrow list) =
  exists_state (arrows_equal m) ms

(*
 * True iff ms doesn't contain m
 *)
let not_contains_arrow (m : arrow) (ms : arrow list) =
  not_state (contains_arrow m) ms

(*
 * Map a function on the source of an arrow
 *)
let map_source (f : context_object -> 'a) (m : arrow) : 'a =
  let (src, _, _) = m in
  f src

(*
 * Map a function on the destination of an arrow
 *)
let map_dest (f : context_object -> 'a) (m : arrow) : 'a =
  let (_, _, dst) = m in
  f dst

(*
 * Map a function on the extension of an arrow
 *)
let map_ext (f : extension -> 'a) (m : arrow) : 'a =
  let (_, e, _) = m in
  f e

(*
 * Map a function on the source of an arrow and return a new arrow
 *)
let map_source_arrow (f : context_object -> context_object) (m : arrow) : arrow =
  let (src, e, dst) = m in
  (f src, e, dst)

(*
 * Map a function on the destination of an arrow and return a new arrow
 *)
let map_dest_arrow (f : context_object -> context_object) (m : arrow) : arrow =
  let (src, e, dst) = m in
  (src, e, f dst)

(*
 * Map a function on the extension of an arrow and return a new arrow
 *)
let map_ext_arrow (f : extension -> extension) (m : arrow) : arrow =
  let (src, e, dst) = m in
  (src, f e, dst)

(*
 * True iff an arrow m maps from o
 *)
let maps_from (o : context_object) (m : arrow) =
  map_source (objects_equal o) m

(*
 * True iff an arrow m maps to o
 *)
let maps_to (o : context_object) (m : arrow) =
  map_dest (objects_equal o) m

(*
 * Return all objects from which an arrow in ms flows
 *)
let hypotheses (ms : arrow list) : context_object list =
  List.map (fun (src, _, _) -> src) ms

(*
 * Return all objects to which an arrow in ms flows
 *)
let conclusions (ms : arrow list) : context_object list =
  List.map (fun (_, _, dst) -> dst) ms

(*
 * Return all objects in os except for the ones that equal except
 *)
let all_objects_except (except : context_object) (os : context_object list) =
  filter_state (objects_not_equal except) os

(*
 * Return all arrows in ms except for the ones that equal except
 *)
let all_arrows_except (except : arrow) (ms : arrow list) =
  filter_state (arrows_not_equal except) ms

(*
 * Return all objects in os except for the ones in except
 *)
let all_objects_except_those_in (except : context_object list) (os : context_object list) =
  filter_state (fun o -> not_contains_object o except) os

(*
 * Return all arrows in ms except for the ones in except
 *)
let all_arrows_except_those_in (except : arrow list) (ms : arrow list) =
  filter_state (fun o -> not_contains_arrow o except) ms

(*
 * Return all arrows from ms that start from src
 *)
let arrows_with_source (src : context_object) (ms : arrow list) =
  filter_state (maps_from src) ms

(*
 * Return all arrows from ms that end with dst
 *)
let arrows_with_dest (dst : context_object) (ms : arrow list) =
  filter_state (maps_to dst) ms

(*
 * Combine os1 and os2 into a single list without duplicates
 *)
let combine_objects (os1 : context_object list) (os2 : context_object list) =
  bind
    (all_objects_except_those_in os1 os2)
    (fun l -> ret (List.append os1 l))

(*
 * Combine ms1 and ms2 into a single list without duplicates
 *)
let combine_arrows (ms1 : arrow list) (ms2 : arrow list) =
  bind
    (all_arrows_except_those_in ms1 ms2)
    (fun l -> ret (List.append ms1 l))

(*
 * Get all of the objects found in ms
 *)
let objects_of_arrows (ms : arrow list) =
  combine_objects (hypotheses ms) (conclusions ms)

(* --- Categories --- *)

let make_category = ProofCat.make
let initial_opt = ProofCat.initial
let terminal_opt = ProofCat.terminal

(* Apply a function to the list of objects of c *)
let map_objects f c =
  bind (objects c) f

(* Apply a function to the list of arrows of c *)
let map_arrows f c =
  f (morphisms c)

(*
 * Destruct c
 *)
let destruct_cat (c : proof_cat) sigma =
  let (sigma, os) = objects c sigma in
  let ms = morphisms c in
  let i = ProofCat.initial c in
  let t = ProofCat.terminal c in
  sigma, (os, ms, i, t)

(*
 * Add an object o to c
 *)
let add_object (o : context_object) (c : proof_cat) =
  bind (destruct_cat c) (fun (os, ms, i, t) -> make_category (o :: os) ms i t)

(*
 * Remove an object o from c
 *)
let remove_object (o : context_object) (c : proof_cat) =
  let get_it ito =
    match ito with
    | Some it ->
       branch_state (objects_equal it) (fun _ -> ret None) (fun _ -> ret ito) o
    | None ->
       ret None
  in
  bind
    (destruct_cat c)
    (fun (os, ms, i, t) ->
      bind
        (all_objects_except o os)
        (fun os' ->
          bind
            (get_it i)
            (fun i' -> bind (get_it t) (make_category os' ms i'))))

(*
 * Add an arrow m to c
 *)
let add_arrow (m : arrow) (c : proof_cat) =
  bind (destruct_cat c) (fun (os, ms, i, t) -> make_category os (m :: ms) i t)

(*
 * Set the initial object of c
 *)
let set_initial (i : initial_object) (c : proof_cat) =
  bind (destruct_cat c) (fun (os, ms, _, t) -> make_category os ms i t)

(*
 * Set the terminal object of c
 *)
let set_terminal (t : terminal_object) (c : proof_cat) =
  bind (destruct_cat c) (fun (os, ms, i, _) -> make_category os ms i t)

(*
 * Set the initial and terminal objects of c
 *)
let set_initial_terminal (i : initial_object) (t : terminal_object) (c : proof_cat) =
  bind (set_initial i c) (set_terminal t)

(*
 * Check whether c has an initial object
 *)
let has_initial (c : proof_cat) : bool =
  Option.has_some (initial_opt c)

(*
 * Check whether c has a terminal object
 *)
let has_terminal (c : proof_cat) : bool =
  Option.has_some (terminal_opt c)

(*
 * Get the initial object of c
 *)
let initial (c : proof_cat) : context_object =
  let i = initial_opt c in
  if Option.has_some i then Option.get i else failwith "no initial object"

(*
 * Get the terminal object c
 *)
let terminal (c : proof_cat) : context_object =
  let t = terminal_opt c in
  if Option.has_some t then Option.get t else failwith "no terminal object"

(*
 * Check whether o is initial in c
 *)
let is_initial (c : proof_cat) (o : context_object) =
  and_state
    (fun c -> ret (has_initial c))
    (fun c -> objects_equal o (initial c))
    c
    c

(*
 * Check whether o is terminal in c
 *)
let is_terminal (c : proof_cat) (o : context_object) =
  and_state
    (fun c -> ret (has_terminal c))
    (fun c -> objects_equal o (terminal c))
    c
    c

(*
 * Combine c1 and c2, setting i as the initial object
 * and t as the terminal object
 *)
let combine (i : initial_object) (t : terminal_object) (c1 : proof_cat) (c2 : proof_cat) sigma =
  let (ms1, ms2) = map_tuple morphisms (c1, c2) in
  let sigma, os1 = objects c1 sigma in
  let sigma, os2 = objects c2 sigma in
  let sigma, os = combine_objects os1 os2 sigma in
  let sigma, ms = combine_arrows ms1 ms2 sigma in
  ProofCat.make os ms i t sigma

(* Check if c contains m *)
let category_contains_arrow (a : arrow) (c : proof_cat) sigma =
  let ms = morphisms c in
  contains_arrow a ms sigma

(* Get the only explicit arrow in c, or fail if it doesn't have one *)
let only_arrow (c : proof_cat) : arrow =
  let ms = morphisms c in
  assert ((List.length ms) = 1);
  List.hd ms

(* Determine if o is a hypothesis in c *)
let is_hypothesis (c : proof_cat) (o : context_object) =
  contains_object o (map_arrows hypotheses c)

(* Determine if o is not a hypothesis in c *)
let is_not_hypothesis (c : proof_cat) (o : context_object) =
  not_state (is_hypothesis c) o

(* --- Paths of explicit (not transitive or identity) arrows --- *)

(*
 * Check if src reaches dst via some explicit path in c
 *)
let has_path (c : proof_cat) (src : context_object) (dst : context_object) =
  let rec reaches ms (s : context_object) (d : context_object) =
    branch_state
      (objects_equal d)
      (fun _ -> ret true)
      (fun s ->
        bind
          (arrows_with_source s ms)
          (fun adj ->
            and_state
              (fun adj -> ret (non_empty adj))
              (fun adj ->
                bind
                  (map_state (map_dest (reaches ms s)) adj)
                  (exists_state (fun s -> ret (id s))))
              adj
              adj))
      s
  in reaches (morphisms c) src dst

(*
 * Get a list of arrows on some path starting from o in c
 *)
let arrows_from (c : proof_cat) (o : context_object) =
  let rec from ms s sigma =
    let sigma, adj = arrows_with_source s ms sigma in
    let sigma, tl = flat_map_state (map_dest (from ms)) adj sigma in
    sigma, List.append adj tl
  in from (morphisms c) o

(*
 * Get a list of explicit arrows on some path between two objects in c, in either order
 * Assumes there are no cycles
 * Maintains order for lists
 *)
let arrows_between (c : proof_cat) (src : context_object) (dst : context_object)sigma =
let rec between ms s d =
  branch_state
    (objects_equal d)
    (fun _ -> ret [])
    (fun s ->
      bind
        (arrows_with_source s ms)
        (fun adj sigma ->
          let sigma, tl = flat_map_state (map_dest (between ms s)) adj sigma in
          sigma, List.append adj tl))
    s
  in
  let ms = morphisms c in
  branch_state
    (has_path c src)
    (between ms src)
    (fun _ ->
      branch_state
        (has_path c dst)
        (between ms dst)
        (fun _ -> ret [])
        src)
    dst

(*
 * Find ordered paths from src in c via explicit arrows
 *)
let paths_from (c : proof_cat) (src : context_object) =
  let rec paths ms s =
    bind
      (arrows_with_source s ms)
      (flat_map_state
         (fun m ->
           bind
             (map_dest (paths ms) m)
             (fun paths ->
               ret
                 (if (List.length paths) = 0 then
                    [[m]]
                  else
                    List.map (fun p -> m :: p) paths))))
  in paths (morphisms c) src

(*
 * TODO move to lib if we still need this after refactor to remove cats
 *)
let find_off (a : 'a list) (p : 'a -> evar_map -> bool state) sigma : int state =
  let rec find_rec a p n =
    match a with
    | [] -> failwith "not found"
    | h :: tl ->
       branch_state
         p
         (fun _ -> ret n)
         (fun _ -> find_rec tl p (n + 1))
         h
  in find_rec a p 0 sigma
           
(*
 * Get the length of the shortest path from the initial context to dst
 * If dst is the initial context, this is 0
 * Error if no initial context
 * Error if dst is unreachable
 *)
let shortest_path_length (c : proof_cat) (o : context_object) sigma : int state =
  let i = initial c in
  let sigma, has_path_bool = has_path c i o sigma in
  assert has_path_bool;
  branch_state
    (objects_equal o)
    (fun _ -> ret 0)
    (fun s sigma ->
      let sigma, paths = paths_from c s sigma in
      let pdsts = List.map conclusions paths in
      let sigma, pdsts_with_o = filter_state (contains_object o) pdsts sigma in
      let sigma, lengths_to_o =
        map_state
          (fun path ->
            bind
              (find_off path (objects_equal o))
              (fun n -> ret (n + 1)))
          pdsts_with_o
          sigma
      in sigma, List.hd (List.sort Pervasives.compare lengths_to_o))
    i
    sigma

(* --- Functors --- *)

module ProofFunctor = Functor (ProofCat) (ProofCat)

(*
 * Apply a functor over proof categories
 *)
let apply_functor fo fa (c : proof_cat) =
  bind
    (ProofFunctor.make fo fa)
    (fun f -> ret (ProofFunctor.apply f c))

