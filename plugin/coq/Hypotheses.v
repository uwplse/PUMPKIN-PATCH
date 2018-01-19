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

Definition expectedPatch1 :=
  fun (n m : nat) (H1 : n < m) =>
    PeanoNat.Nat.lt_le_incl n m H1.

Theorem testPatch1 :
  patch1 = expectedPatch1.
Proof.
  reflexivity.
Qed.

Theorem old2:
  forall (n m p : nat),
    n < m ->
    m <= p ->
    n <= p.
Proof.
  intros. apply PeanoNat.Nat.lt_le_incl in H. induction H0.
  - auto with arith.
  - apply le_S. auto.
Qed.

Definition new2 := new1.

Patch Proof old2 new2 as patch2.

Definition expectedPatch2 :=
  fun (n m : nat) (H1 : n < m) =>
    PeanoNat.Nat.lt_le_incl n m H1.

Theorem testPatch2 :
  patch2 = expectedPatch2.
Proof.
  reflexivity.
Qed.
