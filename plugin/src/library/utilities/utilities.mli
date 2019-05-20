(*
 * Basic utilities for collections, optionals, and so on
 *)

(* --- Optionals --- *)

(*
 * Map a function on an optional, and return a default value if it's none
 * This should be in the standard library, but for some reason locally is not
 *)
val map_default : ('a -> 'b) -> 'b -> 'a option -> 'b

(* --- Lists --- *)

val last : 'a list -> 'a
val all_but_last : 'a list -> 'a list
val snoc : 'a -> 'a list -> 'a list
val map3 : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list

(*
 * Take n elements of a list
 *)
val take : int -> 'a list -> 'a list

(*
 * Take all but n elements of a list
 *)
val take_except : int -> 'a list -> 'a list

(*
 * Split a list l into (l1, l2) where |l1| = n and |l2| = |l| - n
 *)
val take_split : int -> 'a list -> ('a list * 'a list)

(*
 * Remove duplicates from a list
 *)
val unique : ('a -> 'a -> bool) -> 'a list -> 'a list
                                             
(*
 * Map a function over a list, then flatten the result
 *)
val flat_map : ('a -> 'b list) -> 'a list -> 'b list

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
 * [min, max)
 *)
val range : int -> int -> int list

(*
 * [1, max]
 *)
val from_one_to : int -> int list

(* --- Tuples --- *)

val map_tuple : ('a -> 'b) -> ('a * 'a) -> ('b * 'b)
val twice : ('a -> 'a -> bool -> 'b) -> 'a -> 'a -> ('b * 'b)
val reverse: ('a * 'b) -> ('b * 'a)

(* --- Propositions --- *)

val always_true : 'a -> bool
val and_p : ('a -> bool) -> 'a -> 'a -> bool

(* --- Control structures --- *)

val map_if_else : ('a -> 'b) -> ('a -> 'b) -> bool -> 'a -> 'b
val map_if : ('a -> 'a) -> bool -> 'a -> 'a

(* --- Functions --- *)

(*
 * Flip the first and second parameters of a function.
 *)
val flip : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)

(* Look up the name referenced by a term and append a suffix to it. *)
val suffix_term_name : Constr.t -> Names.Id.t -> Names.Id.t

(*
 * The identity function
 *)
val id : 'a -> 'a
