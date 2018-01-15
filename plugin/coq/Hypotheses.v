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
  intros. apply PeanoNat.Nat.lt_le_incl in H. induction H0.
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

(*
 * TODO check result
 *)

Print patch1.

Theorem old2:
  forall (n m p : nat),
    n < m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - auto with arith.
  - apply le_S. auto.
Qed.

Definition new2 := new1.

Patch Proof old2 new2 as patch2.

(*
 * TODO check result
 *)

Print patch2.
