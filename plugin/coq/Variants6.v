(* Seventh variants *)

Require Import Arith NPeano.

Theorem old7_v1 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < p + 1.
Proof.
  intros. rewrite plus_comm. induction H0.
  - auto with arith.
  - constructor. apply IHle.
Qed.

Theorem old7_v2 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < p + 1.
Proof.
  intros. induction H0.
  - rewrite plus_comm. auto with arith.
  - constructor. apply IHle.
Qed.


