(* Examples for patching Theorems *)

Require Import Patcher.Patch.
Require Import Arith NPeano.
Require Import List.

(* ------------------------ *)

Theorem oldT1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Qed.

Theorem newT1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Qed.

Theorem T2:
  forall (m p : nat),
    m <= p ->
    0 <= p + 1.
Proof.
  intros. eapply oldT1; eauto. intuition.
Qed.

Theorem T3:
  forall (p : nat),
    0 <= p + 1.
Proof.
  intros. eapply T2; eauto.
Qed.

(* Change in T2 *)

Patch Theorem oldT1 newT1 T2 as T2'.

Theorem T2Test:
  forall (m p : nat),
    m <= p ->
    0 <= p.
Proof.
  exact T2'.
Qed.

(* Change in T3 *)

Patch Theorem T2 T2' T3 as T3'.

Theorem T3Test:
  forall (p : nat),
     0 <= p.
Proof.
  exact T3'.
Qed.

(* Showing T3 via change in proof of T1 (need to find this automatically) *)

Patch Proof oldT1 newT1 as P1.

Theorem T3Patch:
  forall (p : nat),
     0 <= p + 1.
Proof.
  intros.
  apply (P1 0 0 p (le_n 0) (T2' p p (le_n p)) (PeanoNat.Nat.le_0_l p)).
Qed.

(* -------------------------- *)

Inductive Max : list nat -> nat -> Type :=
  | MaxNil:
      Max nil 0
  | MaxCons:
      forall l n m,
        Max l n ->
        Max (m :: l) (max n m).

Theorem InMaxLeOld:
  forall (n : nat) (m : nat) (l : list nat),
    In n l ->
    Max l m ->
    (n <= m + 1).
Proof.
  intros. induction H0.
  - inversion H.
  - induction H.
    + subst. apply le_plus_trans. apply NPeano.Nat.le_max_r.
    + apply IHMax in H. rewrite H.
      apply plus_le_compat_r.
      apply NPeano.Nat.le_max_l.
Qed.

Theorem InMaxLeNew:
  forall (n : nat) (m : nat) (l : list nat),
    In n l ->
    Max l m ->
    (n <= m).
Proof.
  intros. induction H0.
  - inversion H.
  - induction H.
    + subst. apply NPeano.Nat.le_max_r.
    + apply IHMax in H. rewrite H. apply NPeano.Nat.le_max_l.
Qed.

(* --- A simple example, no lambdas, that requires changing a type --- *)

Definition changeTMinimalOld (a n m : nat) (l0 : list nat) (H : a = n) (H0 : Max (a :: l0) m) :=
  eq_ind_r
    (fun a0 : nat => Max (a0 :: l0) m -> n <= m + 1)
    (InMaxLeOld n m (n :: l0) (or_introl eq_refl))
    H
    H0.

Definition expectedChangeTMinimal (a n m : nat) (l0 : list nat) (H : a = n) (H0 : Max (a :: l0) m) :=
  eq_ind_r 
    (fun a0 : nat => Max (a0 :: l0) m -> n <= m)
    (InMaxLeNew n m (n :: l0) (or_introl eq_refl))
    H 
    H0.

Patch Theorem InMaxLeOld InMaxLeNew changeTMinimalOld as changeTMinimal.

Theorem testChangeTMinimal :
  changeTMinimal = expectedChangeTMinimal.
Proof.
  reflexivity.
Qed.

(* --- A simple example with lambdas that requires changing a type --- *)

Definition changeTMinimalOldLambda (a n m : nat) (l0 : list nat) (H : a = n) (H0 : Max (a :: l0) m) :=
  eq_ind_r
    (fun a0 : nat => Max (a0 :: l0) m -> n <= m + 1)
    (fun (H7 : Max (n :: l0) m) =>
       InMaxLeOld n m (n :: l0) (or_introl eq_refl) H7)
    H
    H0.

Definition expectedChangeTMinimalLambda (a n m : nat) (l0 : list nat) (H : a = n) (H0 : Max (a :: l0) m) :=
  eq_ind_r 
    (fun a0 : nat => Max (a0 :: l0) m -> n <= m)
    (fun (H7 : Max (n :: l0) m) =>
       InMaxLeNew n m (n :: l0) (or_introl eq_refl) H7)
    H 
    H0.

Patch Theorem InMaxLeOld InMaxLeNew changeTMinimalOldLambda as changeTMinimalLambda.

Theorem testChangeTMinimalLambda :
  changeTMinimalLambda = expectedChangeTMinimalLambda.
Proof.
  reflexivity.
Qed.

(* Change in HdMaxLe *)

Theorem HdMaxLeOld:
  forall (n : nat) (m : nat) (l : list nat),
    hd_error l = value n ->
    Max l m ->
    (n <= m + 1).
Proof.
  intros n m.
  induction l; simpl; intros.
  - discriminate.
  - inversion H. subst.
    eapply InMaxLeOld; eauto.
    simpl. left. reflexivity.
Qed.

Patch Theorem InMaxLeOld InMaxLeNew HdMaxLeOld as HdMaxLeNew.

Theorem TestHdMaxLeNew:
  forall (n : nat) (m : nat) (l : list nat),
    hd_error l = value n ->
    Max l m ->
    n <= m.
Proof.
  exact HdMaxLeNew.
Qed.

