(* Implementations of auxiliary functions for lists and arrays *)

(*
 * Creates a list of the range of min to max, excluding max
 * This is an auxiliary function renamed from seq in template-coq
 *)
let rec range (min : int) (max : int) : int list =
  if min < max then
    min :: range (min + 1) max
  else
    []

(*
 * Creates a list from the index 1 to max, inclusive
 *)
let from_one_to (max : int) : int list =
  range 1 (max + 1)

(*
 * This is an auxiliary function from StackOverflow
 * Splits a list at an index
 *)
let rec split_at (n : int) (l : 'a list) : (('a list) * ('a list)) =
  if n = 0 then
    ([], l)
  else
    match l with
      h :: t ->
        let (l1, l2) = split_at (n - 1) t in
        (h :: l1, l2)
    | [] ->
       ([], [])

(*
 * Returns the index of an element that satisfies p in a
 *)
let rec find (a : 'a array) (p : 'a -> bool) (n : int) : int =
  if p (a.(n)) then
    n
  else
    find a p (n + 1)

(*
 * Remove duplicates from a list
 *)
let rec unique (eq : 'a -> 'a -> bool)  (l : 'a list) : 'a list =
  match l with
  | [] -> []
  | h :: t -> h :: (List.filter (fun a -> not (eq h a)) (unique eq t))

(*
 * All combinations of elements in a list
 *)
let rec combinations (l : 'a list) =
  match l with
  | [] -> []
  | h :: t -> List.append (List.map (fun e -> (h, e)) t) (combinations t)

(*
 * Cartesian product of two lists
 * From http://stackoverflow.com/questions/1507496/ocaml-permutation-of-every-value-in-two-sets-how-to-translate-this-from-java
 *)
let cartesian (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list =
  List.concat (List.map (fun a -> List.map (fun b -> (a, b)) l2) l1)

(*
 * Combine all permutations of pairs of elements in lists l1 and l2 via f
 *)
let  combine_cartesian (f : 'a -> 'b -> 'c) (l1 : 'a list) (l2 : 'b list) : 'c list =
  List.map (fun (a, b) -> f a b) (cartesian l1 l2)

(*
 * Turns an array of lists into a list of arrays
 *)
let combine_cartesian_append (al : 'a list array) : 'a array list =
  let al' = Array.to_list (Array.map (List.map (fun a -> [a])) al) in
  if (Array.length al) <= 1 then
    List.map Array.of_list (List.concat al')
  else
    List.map Array.of_list (List.fold_left (combine_cartesian List.append) (List.hd al') (List.tl al'))

(*
 * Gets the last element of l
 *)
let last (l : 'a list) =
  List.hd (List.rev l)

(*
 * Gets all but the last element of l
 *)
let remove_last (l : 'a list) =
  List.rev (List.tl (List.rev l))

(*
 * Map f over a tuple
 *)
let map_tuple (f : 'a -> 'b) ((a1, a2) : ('a * 'a)) : ('b * 'b) =
  (f a1, f a2)

(*
 * Fold f over a tuple
 *)
let fold_tuple (f : 'a -> 'a -> 'b) ((a1, a2) : ('a * 'a)) : 'b =
  f a1 a2

(*
 * Map f and g over a heterogenous tuple
 *)
let map_tuple_hetero (f : 'a -> 'c) (g : 'b -> 'd) ((a, b) : ('a * 'b)) : ('c * 'd) =
  (f a, g b)

(*
 * Map a function over a list, then flatten the result
 *)
let flat_map (f : 'a -> 'b list) (l : 'a list) : 'b list =
  List.flatten (List.map f l)

(*
 * Same as flat_map, but for map2
 *)
let flat_map2 (f : 'a -> 'b -> 'c list) (la : 'a list) (lb : 'b list) : 'c list =
  List.flatten (List.map2 f la lb)

(* Map3 *)
let rec map3 (f : 'a -> 'b -> 'c -> 'd) l1 l2 l3 : 'd list =
  match (l1, l2, l3) with
  | ([], [], []) ->
     []
  | (h1 :: t1, h2 :: t2, h3 :: t3) ->
     let r = f h1 h2 h3 in r :: map3 f t1 t2 t3
  | _ ->
     failwith "illegal call to map3"

(*
 * Get the head of a transformation on a list,
 * defaulting to default if the original list is empty, or if the
 * result is empty
 *)
let hd_f_default (a : 'a) (f : 'a list -> 'a list) (l : 'a list) : 'a =
  if List.length l = 0 then
    a
  else
    let fl = f l in
    if List.length fl = 0 then
      a
    else
      List.hd fl

(*
 * Return true if a list has length > 0
 *)
let non_empty (l : 'a list) : bool =
  List.length l > 0

(* Filter a list of lists by only its non-empty lists *)
let filter_non_empty (l : 'a list) =
  List.filter non_empty l

(*
 * Get values from a list of optionals only if every optional is some
 * Otherwise, return the empty list
 *)
let get_all_or_none (l : 'a option list) : 'a list =
  if List.for_all Option.has_some l then
    List.map Option.get l
  else
    []

(*
 * Get values from a list of optionals for every element that has_some
 * Filter out values that are none
 *)
let get_some (l : 'a option list) : 'a list =
  List.map Option.get (List.filter Option.has_some l)

(*
 * Create a singleton array
 *)
let singleton_array (a : 'a) : 'a array =
  Array.make 1 a

(*
 * Return true if two arrays are the same length
 *)
let same_length (a1 : 'a array) (a2 : 'b array) : bool =
  Array.length a1 = Array.length a2

(*
 * Apply a function which applies to two lists to two arrays
 *)
let apply_to_arrays (f : 'a list -> 'b list -> 'c) a b : 'c =
  f (Array.to_list a) (Array.to_list b)
