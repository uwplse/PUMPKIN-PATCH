Add LoadPath "coq".
Require Import Arith NPeano.
Require Import Patcher.Patch.

(*
 * Changes in hypotheses of inductive proofs
 *)

Theorem old1:
  forall (n m p : nat),
    n < m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - auto with arith.
  - apply le_S. auto.
Qed.

Theorem new1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - auto with arith.
  - apply le_S. auto.
Qed.

Patch Proof old1 new1 as patch1.

Print patch1.

Definition expectedPatch1 :=
  fun (n m p : nat) (H : n <= m) (H1 : n < m) =>
    PeanoNat.Nat.lt_le_incl n m H1.

Theorem testPatch1 :
  patch1 = expectedPatch1.
Proof.
  reflexivity.
Qed.
