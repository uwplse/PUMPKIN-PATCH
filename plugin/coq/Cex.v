Require Import Arith NPeano.

(*
 * Proof of the example from the Section 3 overview
 * where replaying any subset of existing
 * tactics won't work, even if we can determine the
 * goal type (simple example for which the Section 3
 * footnote isn't true).
 *
 * While this is a contrived example, it shows how the general
 * problem of finding a patch between two tactic proofs is at least
 * as difficult as the problem of finding a patch between two proof terms,
 * since the tactic proof can literally be the application of a proof term.
 * In general, tactics can be delicate and rely on contextual information.
 *)

Theorem new:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - auto.
  - constructor. auto.
Qed.

Theorem old:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - apply (le_plus_trans n m 1 H).
  - constructor. auto.
Qed.

(*
 * The difference in tactics alone is useless,
 * even if we pad it with an intros and an auto.
 *)
Theorem patch_diff_tactics:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p ->
    n <= p + 1.
Proof.
  intros. (* apply (le_plus_trans n m 1 H). *)
  (* Error: Unable to unify "n <= m + 1" with "n <= p + 1". *)
Abort.

(*
 * This is because we need to understand that H there referred
 * to the base case, and we need to abstract it to the general case.
 * So we still need a semantic understanding of the proof.
 *)

(*
 * That is, we would need to figure out that we want this:
 *)
Theorem patch_diff_tactics_semantic:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p ->
    n <= p + 1.
Proof.
  intros. apply (le_plus_trans n p 1 H1).
Qed.

(*
 * Which means we need to understand the semantic difference
 * in terms and types which tells us to abstract it by m
 * and then apply it to p. To know that we need to model inductive
 * proofs.
 *)

(*
 * In this case, we can't even replay the exact tactic proof
 * to find a patch that isn't direct:
 *)
Theorem patch_not_direct:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - apply (le_plus_trans n m 1 H).
  - constructor. auto.
Abort.

(*
 * Of course, we could to this:
 *)
Theorem patch_diff_tactics_abstract:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p ->
    n <= p + 1.
Proof.
  intros. apply le_plus_trans. auto.
Qed.

(*
 * But to do that, we need to model the application tactic and understand
 * what it means to abstract it. This would not work for every tactic.
 *
 * For a really simple contrived example, I could write a tactic that works
 * exactly like apply but requires that you supply every argument. Then
 * the problem would be fully reduced to the term case.
 *)

(*
 * The term approach PUMPKIN PATCH uses doesn't rely on the
 * tactics, which makes it orthogonal to whether the tactic
 * proofs refer to specific parts of the proof that change.
 * It's a more generalizable, less ad-hoc approach.
 *
 * Of course, in some cases, replaying the tactics will work.
 * And when we have really powerful high-level tactics, it might
 * make sense to optimize by trying tactics from the proof
 * strategically first. But this is complementary, and it
 * will fail in some cases where the current approach succeeds.
 *
 * This may also be helpful for going back to tactics eventually, even
 * without a tactic like Transport or hint databases. We can, for example,
 * find the patch term, then use the tactics from the existing proofs to
 * determine how to produce tactics that would produce that term.
 *)

(*
 * Of course, a quick proof that the current approach works
 * on this simple proof:
 *)
Require Import Patcher.Patch.
Patch Proof old new as patch.

Theorem testPatch:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p ->
    n <= p + 1.
Proof.
  exact patch.
Qed.
