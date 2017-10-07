Require Import Arith NPeano.

Hint Resolve Nat.le_max_r Nat.le_max_r : arith.

Theorem new8 :
  forall n m n0 : nat,
    m = n ->
    n <= max n0 m.
Proof.
  intros. subst. auto with arith.
Qed.

(* Same as rewrite H *)
Theorem old8_v1 :
  forall  n m n0 : nat,
    m = n ->
    n <= max n0 m + 1.
Proof.
  intros. subst. auto with arith.
Qed.

(* Moves le_plus_trans outside of rewrite *)
Theorem old8_v2 :
  forall  n m n0 : nat,
    m = n ->
    n <= max n0 m + 1.
Proof.
  intros. apply le_plus_trans. subst. auto with arith.
Qed.

(* Rewrite le_plus_trans first *)
Theorem old8_v3 :
  forall  n m n0 : nat,
    m = n ->
    n <= max n0 m + 1.
Proof.
  intros. rewrite le_plus_trans; subst; auto with arith.
Qed.

(* Rewrite le_max_r first *)
Theorem old8_v4 :
  forall  n m n0 : nat,
    m = n ->
    n <= max n0 m + 1.
Proof.
  intros. rewrite Nat.le_max_r. subst. eauto with arith.
Qed.

(* Rewrite by H instead of subst *)
Theorem old8_v5 :
  forall  n m n0 : nat,
    m = n ->
    n <= max n0 m + 1.
Proof.
  intros. rewrite <- H. auto with arith.
Qed.

(* Rewrite by le_plus_trans first *)
Theorem old8_v6 :
  forall  n m n0 : nat,
    m = n ->
    n <= max n0 m + 1.
Proof.
  intros. rewrite <- le_plus_trans; subst; auto with arith.
Qed.


