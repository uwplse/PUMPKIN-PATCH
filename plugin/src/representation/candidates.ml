(* Basic types for proof search *)

open Constr

type candidates = types list

(* Candidates when we fail to find a patch *)
let give_up : candidates =
  []
