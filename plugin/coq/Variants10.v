Require Import Arith NPeano.

(* The other lemma from the case study, useful for the same reason *)

Lemma new11 : forall a b : nat,
  S a + S b = S (S (a + b)).
Proof.
  intros a b.
  induction a.
  reflexivity.
  simpl.
  rewrite <- IHa.
  reflexivity.
Qed.

(* Through a patch *)
Lemma old11_v1 : forall a b : nat,
  S a + (S b + 0) = S (S (a + (b + 0))).
Proof.
  intros a b.
  repeat rewrite <- plus_n_O.
  induction a.
  reflexivity.
  simpl.
  rewrite <- IHa.
  reflexivity.
Qed.

(* In this case, exact same proof, but different hypo; won't see *)

Lemma old11_v2 : forall a b : nat,
  S a + (S b + 0) = S (S (a + (b + 0))).
Proof.
  intros a b.
  induction a.
  reflexivity.
  simpl.
  rewrite <- IHa.
  reflexivity.
Qed.
