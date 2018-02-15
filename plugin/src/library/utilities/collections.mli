(* Auxiliary functions for lists and arrays *)

(*
 * Creates a list of the range of the first int (min) to the second int (max)
 * Does not include the second int
 *)
val range : int -> int -> int list

(*
 * Creates a list of the range from 1 to max, inclusive
 *)
val from_one_to : int -> int list

(*
 * Splits a list at an index into two lists
 *)
val split_at : int -> 'a list -> (('a list) * ('a list))

(*
 * Returns the index of an element that satisfies a proposition in an array
 *)
val find : 'a array -> ('a -> bool) -> int -> int

(*
 * Remove duplicates from a list
 *)
val unique : ('a -> 'a -> bool) -> 'a list -> 'a list

(*
 * All combinations of elements in a list
 *)
val combinations : 'a list -> ('a * 'a) list

(*
 * Cartesian product of two lists
 *)
val cartesian : 'a list -> 'b list -> ('a * 'b) list

(*
 * Combine all permutations of pairs of elements in two lists
 * Use some combinator function to combine them
 *)
val combine_cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

(*
 * Turns an array of lists [[t11, t12] [t21, t22] ..] into a list
 * of arrays [[t11 t21 ..] .. [t11 t22 ..] .. [t12 t21 ..] .. [t12 t22 ..] ..]
 *)
val combine_cartesian_append : 'a list array -> 'a array list

(*
 * Gets the last element of a list
 *)
val last : 'a list -> 'a

(*
 * Gets all elements but the last element of a list
 *)
val remove_last : 'a list -> 'a list

(*
 * Map a function on a tuple
 *)
val map_tuple : ('a -> 'b) -> ('a * 'a) -> ('b * 'b)

(*
 * Fold a function on a tuple
 *)
val fold_tuple : ('a -> 'a -> 'b) -> ('a * 'a) -> 'b

(*
 * Map two functions over a heterogenous tuple
 *)
val map_tuple_hetero:  ('a -> 'c) -> ('b -> 'd) -> ('a * 'b) -> ('c * 'd)

(*
 * Map a function over a list, then flatten the result
 *)
val flat_map : ('a -> 'b list) -> 'a list -> 'b list

(*
 * Same as flat_map, but for map2
 *)
val flat_map2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list

(*
 * Map3
 *)
val map3 : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list

(*
 * Get the head of a transformation on a list,
 * defaulting to default if the list is empty
 *)
val hd_f_default : 'a -> ('a list -> 'a list) -> 'a list -> 'a

(*
 * Filter a list of lists by only its non-empty lists
 *)
val filter_non_empty : 'a list list -> 'a list list

(*
 * Get values from a list of optionals only if every optional is some
 * Otherwise, return the empty list
 *)
val get_all_or_none : 'a option list -> 'a list

(*
 * Get values from a list of optionals for every element that has_some
 * Filter out values that are none
 *)
val get_some : 'a option list -> 'a list

(*
 * Create a singleton array
 *)
val singleton_array : 'a -> 'a array

(*
 * Return true if a list has at least one element
 *)
val non_empty : 'a list -> bool

(*
 * Return true if two arrays are the same length
 *)
val same_length : 'a array -> 'b array -> bool

(*
 * Apply a function which applies to two lists to two arrays
 *)
val apply_to_arrays :
  ('a list -> 'b list -> 'c) -> 'a array -> 'b array -> 'c
