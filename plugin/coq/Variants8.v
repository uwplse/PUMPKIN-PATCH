Require Import Arith NPeano.

Hint Resolve Nat.le_max_l Nat.le_max_r : arith.

(* Can't do this, since we don't unwrap functions *)
Theorem old9_v1 :
  forall  n m n0 : nat,
    m = n ->
    n <= max m n0.
Proof.
  intros. subst. auto with arith.
Qed.

(* Fails because of rewrite <- H *)
Theorem old9_v2 :
  forall  n m n0 : nat,
    m = n ->
    n <= max m n0.
Proof.
  intros. rewrite Nat.max_comm. rewrite <- H. auto with arith.
Qed.

(* On the other hand: *)
Theorem old9_v3 :
  forall  n m n0 : nat,
    m = n ->
    n <= max m n0.
Proof.
  intros. subst. rewrite Nat.max_comm. auto with arith.
Qed.

(* And also: *)
Theorem old9_v4 :
  forall  n m n0 : nat,
    m = n ->
    n <= max m n0.
Proof.
  intros. rewrite Nat.max_comm. subst. auto with arith.
Qed.

(* I don't show more variants here with rewrite <- H, since that's redundant *)
