Require Import Patcher.Patch.
Require Import Arith NPeano.
Require Import List.

(* Simple difference in inductive proofs *)

(* ------------------------ *)

Theorem old1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - auto with arith.
  - constructor. auto.
Qed.

Theorem new1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - auto with arith.
  - constructor. auto.
Qed.

(* ------------------------- *)

Theorem old2 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Qed.

Theorem new2 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Qed.

(* ------------------------- *)

Theorem old3 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Qed.

Theorem new3 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Qed.

(* ------------------------- *)

Theorem old4 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < p + 1.
Proof.
  intros. induction H0.
  - rewrite plus_comm. auto with arith.
  - constructor. apply IHle.
Qed.

Theorem new4 :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0.
  - auto with arith.
  - constructor. apply IHle.
Qed.

(* -------------------------------- *)

Inductive ListSum : list nat -> nat -> Type :=
| ListSumNil :
    ListSum nil 0
| ListSumCons :
    forall (h : nat) (tl : list nat) (n : nat),
       ListSum tl n ->
       ListSum (h :: tl) (h + n).

Theorem old5 :
  forall (n m : nat) (l1 l2 : list nat),
    ListSum l1 n ->
    ListSum (l1 ++ l2) (n + m) ->
    ListSum (rev (rev l2)) m.
Proof.
  intros. induction H.
  - rewrite rev_involutive. apply H0.
  - inversion H0. subst.
    rewrite plus_assoc_reverse in H4.
    assert (n0 = n + m).
    + eapply plus_reg_l; eauto.
    + subst. apply IHListSum in H2. apply H2.
Qed.

Theorem new5 :
   forall (n m : nat) (l1 l2 : list nat),
     ListSum l1 n ->
     ListSum (l1 ++ l2) (n + m) ->
     ListSum l2 m.
Proof.
  intros. induction H.
  - apply H0.
  - inversion H0. subst.
    rewrite plus_assoc_reverse in H4.
    assert (n0 = n + m).
    + eapply plus_reg_l; eauto.
    + subst. apply IHListSum in H2. apply H2.
Qed.

(* -------------------------------- *)

Theorem old6:
  forall l1 l2 : list nat,
    length (rev (l1 ++ l2)) = (length (rev l1)) + (length (rev l2)).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - repeat rewrite -> rev_length in *. simpl.
    rewrite -> IHl1'. reflexivity.
Qed.

Theorem new6:
  forall l1 l2 : list nat,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

(* -------------------------------- *)

Theorem old7 :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (rev (map f l)).
Proof.
  intros A B f l x. rewrite <- in_rev.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem new7 :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H' | H'].
    + rewrite H'. left. reflexivity.
    + right. apply IHl'. apply H'.
Qed.

(* ----------------------------- *)

Definition old8 (n m n0 : nat) (H : eq m n) :=
  Coq.Init.Logic.eq_ind_r
    (fun (m : nat) => (le n (Coq.Init.Nat.add (Coq.Init.Nat.max n0 m) (S O))))
    (Coq.Arith.Plus.le_plus_trans
       n
       (Coq.Init.Nat.max n0 n)
       (S O)
       (Coq.Arith.PeanoNat.Nat.le_max_r n0 n))
     H.

Definition new8 (n m n0 : nat) (H : eq m n) :=
  Coq.Init.Logic.eq_ind_r
    (fun (m : nat) => (le n (Coq.Init.Nat.max n0 m)))
    (Coq.Arith.PeanoNat.Nat.le_max_r n0 n)
    H.

(* ----------------------------------- *)

(* Tool cannot support this yet, needs backup search: 

(* ORIGINAL *)
Theorem old8:
  forall b1 b2,
    andb b1 b2 = true -> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. intros H. destruct b1; destruct b2.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - discriminate.
Qed.

(* MODIFIED *)
Theorem new8 :
  forall b1 b2,
    andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. intros H. destruct b1; destruct b2; split; try reflexivity; discriminate.
Qed.
*)

