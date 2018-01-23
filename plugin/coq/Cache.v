Require Import Patcher.Patch.

Lemma addn1 : forall n, S n = n + 1.
  intro n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma le_lt : forall n m, S n <= m -> n < m .
  intros n m H. assumption.
Qed.

Register Patch Lemma addn1.
Register Patch Lemma le_lt.

Unregister Patch Lemma addn1.
Unregister Patch Lemma le_lt.