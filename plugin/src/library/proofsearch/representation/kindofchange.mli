(* --- Kinds of changes --- *)

open Term
open Cutlemma

(*
 * Represents the kind of change we are searching for, for now either:
 * 1) A change in conclusions, or
 * 2) A change in an inductive type we are doing induction over that preserves
 *    the shape of the inductive type
 * 3) A change in a fixpoint
 *    definition we are proving a property about inductively
 *    that preserves the shape of the definition
 * 4) A change in conclusions of a case of an inductive type that definitely
 *    cannot be factored out (or that the user does not want to factor out),
 *    as in sum-like inductive types like exists
 * 5) A change in hypotheses (that isn't an inductive type we are inducting
 *    over)
 *)
type kind_of_change =
  | Conclusion
  | InductiveType of types * types
  | FixpointCase of (types * types) * cut_lemma
  | ConclusionCase of (cut_lemma option)
  | Hypothesis of types * types

val is_conclusion : kind_of_change -> bool
val is_inductive_type : kind_of_change -> bool
val is_fixpoint_case : kind_of_change -> bool
val is_conclusion_case : kind_of_change -> bool
val is_hypothesis : kind_of_change -> bool
