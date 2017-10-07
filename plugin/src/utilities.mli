(* Miscellaneous utility functions *)

(*
 * Get a fresh constant identifier
 *)
val fid : unit -> int

(*
 * The identity function
 *)
val id : 'a -> 'a

(*
 * Always return the first argument, given any 'a
 *)
val always : 'b -> 'a -> 'b

(*
 * Test a predicate on a 'a
 * If it is true, apply the first function
 * Otherwise, apply the second function
 *)
val map_if : ('a -> bool) -> ('a -> 'b) -> ('a -> 'b) -> 'a -> 'b

(* Join two predicates by and *)
val and_p : ('a -> bool) -> ('a -> bool) -> 'a -> bool

(* Join two predicates by or *)
val or_p : ('a -> bool) -> ('a -> bool) -> 'a -> bool
