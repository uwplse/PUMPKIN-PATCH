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

(*
 * TODO check result
 *)

Print patch1.
