Require Import Arith NPeano List.

Inductive ListSum : list nat -> nat -> Type :=
| ListSumNil :
    ListSum nil 0
| ListSumCons :
    forall (h : nat) (tl : list nat) (n : nat),
       ListSum tl n ->
       ListSum (h :: tl) (h + n).

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

Theorem old5_v1 :
  forall (n m : nat) (l1 l2 : list nat),
    ListSum l1 n ->
    ListSum (l1 ++ l2) (n + m) ->
    ListSum (rev (rev l2)) m.
Proof.
  intros. rewrite rev_involutive. induction H.
  - apply H0.
  - inversion H0. subst.
    rewrite plus_assoc_reverse in H4.
    assert (n0 = n + m).
    + eapply plus_reg_l; eauto.
    + subst. apply IHListSum in H2. apply H2.
Qed.

Theorem old5_v2 :
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

