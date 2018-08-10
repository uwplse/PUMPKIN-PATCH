(* --- Kinds of changes --- *)

open Constr
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
 * 5) A change in a single hypotheses
 *    (that isn't an inductive type we are inducting over)
 *)
type kind_of_change =
  | Conclusion
  | InductiveType of types * types
  | FixpointCase of (types * types) * cut_lemma
  | ConclusionCase of (cut_lemma option)
  | Hypothesis of types * types

let is_conclusion c =
  c = Conclusion

let is_inductive_type c =
  match c with
  | InductiveType (_, _) -> true
  | _ -> false

let is_fixpoint_case c =
  match c with
  | FixpointCase ((_, _), _) -> true
  | _ -> false

let is_conclusion_case c =
  match c with
  | ConclusionCase _ -> true
  | _ -> false

let is_hypothesis c =
  match c with
  | Hypothesis (_, _) -> true
  | _ -> false
