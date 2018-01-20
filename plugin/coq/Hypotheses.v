Add LoadPath "coq".
Require Import Arith NPeano.
Require Import Patcher.Patch.
Require Import String.
Open Scope string_scope.

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

Theorem testPatch1:
  forall n m,
    n < m ->
    n <= m.
Proof.
  exact patch1.
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

Theorem testPatch2:
  forall n m,
    n < m ->
    n <= m.
Proof.
  exact patch2.
Qed.

Theorem old3 :
  forall (n m p : nat),
    n < m + 1 ->
    m <= p ->
    n <= p.
Proof.
  intros. rewrite plus_comm in H. induction H0.
  - auto with arith.
  - constructor. apply IHle.
Qed.

Definition new3 := new1.

Patch Proof old3 new3 as patch3.

Theorem testPatch3:
  forall n m,
    n < m + 1 ->
    n <= m.
Proof.
  exact patch3.
Qed.

(* --- Invertible changes in hypotheses --- *)

Definition old4 := old3.

Theorem new4 :
  forall (n m p : nat),
    n < S m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - auto with arith.
  - constructor. apply IHle.
Qed.

(*
 * This doesn't work yet. To fix it, we need to check on primitive differencing
 * to see if it's making simplifying assumptions about how to difference
 * in this case.
 *)
Patch Proof old4 new4 as patch4.
Patch Proof new4 old4 as patch4_inv.

Theorem testPatch4:
  forall n m,
    n < m + 1 ->
    n < S m.
Proof.
  exact patch4.
Qed.

Theorem testPatch4_inv:
  forall n m,
    n < S m ->
    n < m + 1.
Proof.
  exact patch4_inv.
Qed.

