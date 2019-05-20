open Util

(*
 * Basic utilities for collections, optionals, and so on
 *)

(*
 * TODO remove unused functions from DEVOID and organize
 *)

(* This should be in the standard library, but isn't bound for some reason *)
let map_default f default x =
  if Option.has_some x then f (Option.get x) else default

(* Get the last element of a list *)
let last (l : 'a list) : 'a =
  List.hd (List.rev l)

(* Get all but the last element of a list *)
let all_but_last (l : 'a list) : 'a list =
  List.rev (List.tl (List.rev l))

(* Snoc *)
let snoc (a : 'a) (l : 'a list) : 'a list =
  List.append l [a]

(* Take n elements of a list *)
let rec take (i : int) (l : 'a list) : 'a list =
  if i = 0 then
    []
  else
    match l with
    | [] ->
       []
    | h :: tl ->
       h :: (take (i - 1) tl)

(* Take all but n elements of a list *)
let take_except (i : int) (l : 'a list) : 'a list =
  take (List.length l - i) l

(* Like take, but return the remainder too *)
let rec take_split (i : int) (l : 'a list) : ('a list * 'a list) =
  if i = 0 then
    ([], l)
  else
    match l with
    | [] ->
       ([], [])
    | h :: tl ->
       let (before, after) = take_split (i - 1) tl in
       (h :: before, after)

(*
 * Remove duplicates from a list
 *)
let rec unique (eq : 'a -> 'a -> bool)  (l : 'a list) : 'a list =
  match l with
  | [] -> []
  | h :: t -> h :: (List.filter (fun a -> not (eq h a)) (unique eq t))

(*
 * Map a function over a list, then flatten the result
 *)
let flat_map (f : 'a -> 'b list) (l : 'a list) : 'b list =
  List.flatten (List.map f l)

(*
 * Cartesian product of two lists
 * From http://stackoverflow.com/questions/1507496/ocaml-permutation-of-every-value-in-two-sets-how-to-translate-this-from-java
 *)
let cartesian (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list =
  List.concat (List.map (fun a -> List.map (fun b -> (a, b)) l2) l1)

(*
 * Combine all permutations of pairs of elements in lists l1 and l2 via f
 *)
let combine_cartesian (f : 'a -> 'b -> 'c) (l1 : 'a list) (l2 : 'b list) : 'c list =
  List.map (fun (a, b) -> f a b) (cartesian l1 l2)
               
(* Map f over a tuple *)
let map_tuple (f : 'a -> 'b) ((a1, a2) : ('a * 'a)) : ('b * 'b) =
  (f a1, f a2)

(* Apply a function twice with a directionality indicator *)
let twice (f : 'a -> 'a -> bool -> 'b) (a1 : 'a) (a2 : 'a) : 'b * 'b  =
  let forward = f a1 a2 true in
  let backward = f a2 a1 false in
  (forward, backward)

(* Reverse a tuple *)
let reverse ((a, b) : 'a * 'b) : 'b * 'a =
  (b, a)

(* Map3 *)
let rec map3 (f : 'a -> 'b -> 'c -> 'd) l1 l2 l3 : 'd list =
  match (l1, l2, l3) with
  | ([], [], []) ->
     []
  | (h1 :: t1, h2 :: t2, h3 :: t3) ->
     let r = f h1 h2 h3 in r :: map3 f t1 t2 t3

(*
 * Creates a list of the range of min to max, excluding max
 * This is an auxiliary function renamed from seq in template-coq
 *)
let rec range (min : int) (max : int) : int list =
  if min < max then
    min :: range (min + 1) max
  else
    []

(* Creates a list from the index 1 to max, inclusive *)
let from_one_to (max : int) : int list =
  range 1 (max + 1)

(* Always true *)
let always_true _ = true

(* Check that p a and p b are both true *)
let and_p (p : 'a -> bool) (o : 'a) (n : 'a) : bool =
  p o && p n

(* Control structures *)
let map_if_else f g b x = if b then f x else g x
let map_if f b x = map_if_else f (fun a -> a) b x

(* Flip the first and second parameters of a function. *)
let flip f = fun x y -> f y x

(* Look up the name referenced by a term and append a suffix to it. *)
let suffix_term_name term suffix =
  let base = Nametab.basename_of_global (Globnames.global_of_constr term) in
  Nameops.add_suffix base (Names.Id.to_string suffix)

(*
 * The identity function
 *)
let id (a : 'a) =
  a
