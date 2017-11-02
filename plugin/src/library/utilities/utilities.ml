(* Miscellaneous utility functions *)

(* Constant ID *)
let k_fresh = ref (1)

(*
 * Get a fresh constant identifier
 *)
let fid () : int =
  let id = !k_fresh in
  k_fresh := id + 1;
  id

(*
 * The identity function
 *)
let id (x : 'a) : 'a =
  x

(*
 * Always return b, given any a
 *)
let always (b : 'b) (_ : 'a) : 'b =
  b

(*
 * Test p on a
 * If it is true, apply f_true
 * Otherwise, apply f_false
 *)
let map_if (p : 'a -> bool) (f_true : 'a -> 'b) (f_false : 'a -> 'b) (a : 'a) : 'b =
  (if p a then f_true else f_false) a

(* Join two predicates by and *)
let and_p (p1 : 'a -> bool) (p2 : 'a -> bool) (a : 'a) : bool =
  p1 a && p2 a

(* Join two predicates by or *)
let or_p (p1 : 'a -> bool) (p2 : 'a -> bool) (a : 'a) : bool =
  p1 a || p2 a
