(* Variants for sixth proof *)

Require Import Arith NPeano List.

Theorem new6:
  forall l1 l2 : list nat,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem old6_v1:
  forall l1 l2 : list nat,
    length (rev (l1 ++ l2)) = (length (rev l1)) + (length (rev l2)).
Proof.
  intros l1 l2.
  repeat rewrite rev_length.
  induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem old6_v2:
  forall l1 l2 : list nat,
    length (rev (l1 ++ l2)) = (length (rev l1)) + (length (rev l2)).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - repeat rewrite -> rev_length in *. simpl.
    rewrite -> IHl1'. reflexivity.
Qed.

