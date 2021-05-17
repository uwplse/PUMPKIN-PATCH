Add LoadPath "coq".
Require Import Patcher.Patch.
Require Import PeanoNat List.
Import ListNotations.
Require Import Omega.



Theorem ex : forall y : nat, (forall x : nat, 0 = 0) /\
             (forall x : nat, 0 = 0).
Proof.
intro y.
split.
- intro. reflexivity.
- intro. reflexivity.
Qed.
Decompile ex.


Theorem example_2 : 
  { z : nat &
  (forall x : nat, x = z -> x = z) /\
  (forall x : nat, x = z -> z = x) }.
Proof.
exists 0.
split. 
- intros x H.
  apply H.
- intros x H.
  symmetry. 
  apply H.
Qed.
Print example_2.
Decompile example_2.

Theorem t1 : forall (A : Type) (a b : A), a = b -> b = a.
Proof.
intros A a b H.
rewrite H.
reflexivity.
Qed.

Theorem t2 : forall (A : Type) (a b : A), a = b -> b = a.
Proof.
intros A a b H.
rewrite <- H.
reflexivity.
Qed.

Decompile t1.
Decompile t2.


Theorem t3 : forall (X : Prop), False -> X.
Proof.
intros X H.
induction H as [].
Qed.

Decompile t3.

Theorem t4 : 0 = 0 /\ 1 = 1.
Proof.
split.
- reflexivity.
- reflexivity.
Qed.

Decompile t4.

Theorem t5 : forall (n : nat), n = 0 \/ n <> 0.
Proof.
intro n.
induction n.
- left. reflexivity.
- right. intro. inversion H.
Qed.

Decompile t5 with "inversion H".


Theorem t6 : forall P Q : Prop, P \/ Q -> P \/ Q .
Proof.
intros P Q H.
induction H as [H0 | H0].
- left. apply H0.
- right. apply H0.
Qed.

Decompile t6.





Theorem f1 : forall (n : nat), n + O = n.
Proof.
intro n.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

(* no simpl *)
Fail Decompile f1.


