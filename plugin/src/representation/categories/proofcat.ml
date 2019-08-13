(* Proof categories, core logic *)

open Category
open Constr
open Environ
open Evd
open Printing
open Assumptions
open Utilities
open Merging

(*
 * Note: Evar discipline is currently very bad here. But, we will eventually
 * get rid of this representation, so it is not worth fixing in the meantime.
 *)

(* --- TODO for backwards compatibility during refactor, fix w/ evar_map updates --- *)

let convertible env sigma t1 t2 = snd (Convertibility.convertible env sigma t1 t2)
let types_convertible env sigma t1 t2 = snd (Convertibility.types_convertible env sigma t1 t2)

(* --- End TODO --- *)
       
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
    | Context (ctx, i) -> Printf.sprintf "%s [%s]" (ctx_as_string ctx) (string_of_int i)

  (* For now we just trust IDs, later if we want we can change this *)
  let ctx_equal (ctx1 : type_context) (ctx2 : type_context) =
    true

  let equal (c1 : t) (c2 : t) =
    let Context (ctx1, i1) = c1 in
    let Context (ctx2, i2) = c2 in
    (i1 = i2) && (ctx_equal ctx1 ctx2)
end

module Extension =
struct
  type t = extension

 (* Prints an extension edge *)
  let rec as_string (e : t) =
    match e with
    | AnonymousBinding -> "Anonymous"
    | Index i -> Printf.sprintf "(Rel %d)" i
    | InductiveHypothesis i -> Printf.sprintf "(IH %d)" i
    | LazyBinding (trm, env) -> term_as_string env trm
    | AppBinding (e1, e2) -> Printf.sprintf "(%s %s)" (as_string e1) (as_string e2)

  let rec equal (e1 : t) (e2 : t) =
    match (e1, e2) with
    | (LazyBinding(trm1, env1), LazyBinding(trm2, env2)) ->
       if env1 == env2 then
         convertible env1 Evd.empty trm1 trm2
       else
         let (env, trm1s, trm2s) = merge_closures (env1, [trm1]) (env2, [trm2]) no_assumptions in
         convertible env Evd.empty (List.hd trm1s) (List.hd trm2s)
    | (AppBinding (e11, e21), AppBinding (e12, e22)) ->
       equal e11 e12 && equal e12 e22 (* imperfect *)
    | _ ->
       e1 = e2
end

(* Categories *)
module ProofCat = Category (TypeContext) (Extension)
type proof_cat = ProofCat.cat
type arrow = ProofCat.arrow

(* Initial category *)
let initial_category : proof_cat =
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
let objects_equal (o1 : context_object) (o2 : context_object) : bool =
  TypeContext.equal o1 o2

(*
 * True iff o1 and o2 are not equal
 *)
let objects_not_equal (o1 : context_object) (o2 : context_object) : bool =
  not (objects_equal o1 o2)

(*
 * True iff os contains o
 *)
let contains_object (o : context_object) (os : context_object list) : bool =
  List.exists (objects_equal o) os

(*
 * True iff os doesn't contain o
 *)
let not_contains_object (o : context_object) (os : context_object list): bool =
  not (contains_object o os)

(*
 * True iff e1 and e2 are equal
 *)
let extensions_equal (e1 : extension) (e2 : extension) : bool =
  Extension.equal e1 e2

(*
 * True iff e1 and e2 are not equal
 *)
let extensions_not_equal (e1 : extension) (e2 : extension) : bool =
  not (extensions_equal e1 e2)

(* Check if two extensions are equal with a set of assumptions *)
let rec extensions_equal_assums (e1 : extension) (e2 : extension) (assums : equal_assumptions) =
  match (e1, e2) with
  | (LazyBinding(trm1, env1), LazyBinding(trm2, env2)) ->
     if env1 == env2 then
       convertible env1 Evd.empty trm1 trm2
     else
       let (env, trm1s, trm2s) = merge_closures (env1, [trm1]) (env2, [trm2]) assums in
       convertible env Evd.empty (List.hd trm1s) (List.hd trm2s)
  | (AppBinding (e11, e21), AppBinding (e12, e22)) ->
     extensions_equal_assums e11 e12 assums
     && extensions_equal_assums e12 e22 assums (* imperfect *)
  | _ ->
     e1 = e2

(*
 * True iff a1 and a2 are equal
 *)
let arrows_equal (m1 : arrow) (m2 : arrow) : bool =
  let (src1, e1, dst1) = m1 in
  let (src2, e2, dst2) = m2 in
  objects_equal src1 src2 && extensions_equal e1 e2 && objects_equal dst1 dst2

(*
 * True iff a1 and a2 are not equal
 *)
let arrows_not_equal (m1 : arrow) (m2 : arrow) : bool =
  not (arrows_equal m1 m2)

(*
 * True iff ms contains m
 *)
let contains_arrow (m : arrow) (ms : arrow list) : bool =
  List.exists (arrows_equal m) ms

(*
 * True iff ms doesn't contain m
 *)
let not_contains_arrow (m : arrow) (ms : arrow list) : bool =
  not (contains_arrow m ms)

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
let maps_from (o : context_object) (m : arrow) : bool =
  map_source (objects_equal o) m

(*
 * True iff an arrow m maps to o
 *)
let maps_to (o : context_object) (m : arrow) : bool =
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
let all_objects_except (except : context_object) (os : context_object list) : context_object list =
  List.filter (objects_not_equal except) os

(*
 * Return all arrows in ms except for the ones that equal except
 *)
let all_arrows_except (except : arrow) (ms : arrow list) : arrow list =
  List.filter (arrows_not_equal except) ms

(*
 * Return all objects in os except for the ones in except
 *)
let all_objects_except_those_in (except : context_object list) (os : context_object list) : context_object list =
  List.filter (fun o -> not_contains_object o except) os

(*
 * Return all arrows in ms except for the ones in except
 *)
let all_arrows_except_those_in (except : arrow list) (ms : arrow list) : arrow list =
  List.filter (fun o -> not_contains_arrow o except) ms

(*
 * Return all arrows from ms that start from src
 *)
let arrows_with_source (src : context_object) (ms : arrow list) : arrow list =
  List.filter (maps_from src) ms

(*
 * Return all arrows from ms that end with dst
 *)
let arrows_with_dest (dst : context_object) (ms : arrow list) : arrow list =
  List.filter (maps_to dst) ms

(*
 * Combine os1 and os2 into a single list without duplicates
 *)
let combine_objects (os1 : context_object list) (os2 : context_object list) : context_object list =
  List.append os1 (all_objects_except_those_in os1 os2)

(*
 * Combine ms1 and ms2 into a single list without duplicates
 *)
let combine_arrows (ms1 : arrow list) (ms2 : arrow list) : arrow list =
  List.append ms1 (all_arrows_except_those_in ms1 ms2)

(*
 * Get all of the objects found in ms
 *)
let objects_of_arrows (ms : arrow list) : context_object list =
  combine_objects (hypotheses ms) (conclusions ms)

(* --- Categories --- *)

let make_category = ProofCat.make
let initial_opt = ProofCat.initial
let terminal_opt = ProofCat.terminal

(* Apply a function to the list of objects of c *)
let map_objects (f : context_object list -> 'a) (c : proof_cat) : 'a =
  f (objects c)

(* Apply a function to the list of arrows of c *)
let map_arrows (f : arrow list -> 'a) (c : proof_cat) : 'a =
  f (morphisms c)

(*
 * Destruct c
 *)
let destruct_cat (c : proof_cat) =
  let os = objects c in
  let ms = morphisms c in
  let i = ProofCat.initial c in
  let t = ProofCat.terminal c in
  (os, ms, i, t)

(*
 * Add an object o to c
 *)
let add_object (o : context_object) (c : proof_cat) : proof_cat =
  let (os, ms, i, t) = destruct_cat c in
  make_category (o :: os) ms i t

(*
 * Remove an object o from c
 *)
let remove_object (o : context_object) (c : proof_cat) : proof_cat =
  let (os, ms, i, t) = destruct_cat c in
  let get_it ito =
    match ito with
    | Some it -> if objects_equal it o then None else ito
    | None -> None
  in make_category (all_objects_except o os) ms (get_it i) (get_it t)

(*
 * Add an arrow m to c
 *)
let add_arrow (m : arrow) (c : proof_cat) : proof_cat =
  let (os, ms, i, t) = destruct_cat c in
  make_category os (m :: ms) i t

(*
 * Set the initial object of c
 *)
let set_initial (i : initial_object) (c : proof_cat) : proof_cat =
  let (os, ms, _, t) = destruct_cat c in
  make_category os ms i t

(*
 * Set the terminal object of c
 *)
let set_terminal (t : terminal_object) (c : proof_cat) : proof_cat =
  let (os, ms, i, _) = destruct_cat c in
  make_category os ms i t

(*
 * Set the initial and terminal objects of c
 *)
let set_initial_terminal (i : initial_object) (t : terminal_object) (c : proof_cat) : proof_cat =
  set_terminal t (set_initial i c)

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
let is_initial (c : proof_cat) (o : context_object) : bool =
  has_initial c && objects_equal o (initial c)

(*
 * Check whether o is terminal in c
 *)
let is_terminal (c : proof_cat) (o : context_object) : bool =
  has_terminal c && objects_equal o (terminal c)

(*
 * Combine c1 and c2, setting i as the initial object
 * and t as the terminal object
 *)
let combine (i : initial_object) (t : terminal_object) (c1 : proof_cat) (c2 : proof_cat) : proof_cat =
  let (os1, os2) = (objects c1, objects c2) in
  let (ms1, ms2) = (morphisms c1, morphisms c2) in
  let os = combine_objects os1 os2 in
  let ms = combine_arrows ms1 ms2 in
  ProofCat.make os ms i t

(* Check if c contains m *)
let category_contains_arrow (a : arrow) (c : proof_cat) : bool =
  let ms = morphisms c in
  contains_arrow a ms

(* Get the only explicit arrow in c, or fail if it doesn't have one *)
let only_arrow (c : proof_cat) : arrow =
  let ms = morphisms c in
  assert ((List.length ms) = 1);
  List.hd ms

(* Determine if o is a hypothesis in c *)
let is_hypothesis (c : proof_cat) (o : context_object) : bool =
  contains_object o (map_arrows hypotheses c)

(* Determine if o is not a hypothesis in c *)
let is_not_hypothesis (c : proof_cat) (o : context_object) : bool =
  not (is_hypothesis c o)

(* --- Paths of explicit (not transitive or identity) arrows --- *)

(*
 * Check if src reaches dst via some explicit path in c
 *)
let has_path (c : proof_cat) (src : context_object) (dst : context_object) : bool =
  let rec reaches ms (s : context_object) (d : context_object) =
    map_if_else
      (always_true)
      (fun d' ->
        let reaches_rec = fun s' -> reaches ms s' d' in
        let adj = arrows_with_source s ms in
        non_empty adj && List.exists id (List.map (map_dest reaches_rec) adj))
      (objects_equal s d)
      d
  in reaches (morphisms c) src dst

(*
 * Get a list of arrows on some path starting from o in c
 *)
let arrows_from (c : proof_cat) (o : context_object) : arrow list =
  let rec from ms s =
    let adj = arrows_with_source s ms in
    List.append adj (flat_map (map_dest (from ms)) adj)
  in from (morphisms c) o

(*
 * Get a list of explicit arrows on some path between two objects in c, in either order
 * Assumes there are no cycles
 * Maintains order for lists
 *)
let arrows_between (c : proof_cat) (src : context_object) (dst : context_object) : arrow list =
  let rec between ms s d =
    map_if_else
      (fun _ -> [])
      (fun d' ->
        let between_rec = fun s' -> between ms s' d' in
        let adj = arrows_with_source s ms in
        List.append adj (flat_map (map_dest between_rec) adj))
      (objects_equal s d)
      d
  in
  let ms = morphisms c in
  if has_path c src dst then
    between ms src dst
  else if has_path c dst src then
    between ms dst src
  else
    []

(*
 * Find ordered paths from src in c via explicit arrows
 *)
let paths_from (c : proof_cat) (src : context_object) : arrow list list =
  let rec paths ms s =
    let adj = arrows_with_source s ms in
    flat_map
      (fun m ->
        let paths = map_dest (paths ms) m in
        if (List.length paths) = 0 then
          [[m]]
        else
          List.map (fun p -> m :: p) paths)
      adj
  in paths (morphisms c) src

(*
 * Get the length of the shortest path from the initial context to dst
 * If dst is the initial context, this is 0
 * Error if no initial context
 * Error if dst is unreachable
 *)
let shortest_path_length (c : proof_cat) (o : context_object) : int =
  let i = initial c in
  assert (has_path c i o);
  let is_o = objects_equal o in
  let contains_o = contains_object o in
  map_if_else
    (fun _ -> 0)
    (fun s ->
      let pdsts = List.map conclusions (paths_from c s) in
      let pdsts_with_o = List.filter contains_o pdsts in
      let lengths_to_o =
        List.map
          (fun path -> find_off path is_o + 1)
          pdsts_with_o
      in List.hd (List.sort Pervasives.compare lengths_to_o))
    (is_o i)
    i

(* --- Functors --- *)

module ProofFunctor = Functor (ProofCat) (ProofCat)

(*
 * Apply a functor over proof categories
 *)
let apply_functor (fo : context_object -> context_object) (fa : arrow -> arrow) (c : proof_cat) =
  let f = ProofFunctor.make fo fa in
  ProofFunctor.apply f c

