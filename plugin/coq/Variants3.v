(* Variants for forth proof *)

Require Import Arith NPeano.

(* In this case, both are as strong as possible, but one direction
   is "more natural" than the other *)

Theorem new4 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0; auto.
Qed.

(* Outside, conclusion, function *)

Theorem old4_v1 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. apply le_lt_n_Sm. induction H0; auto.
Qed.

(* Inside, conclusion, function *)

Theorem old4_v2 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0; auto with arith.
Qed.
