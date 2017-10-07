Require Import Arith NPeano.

(* Variants of proof from case study.
   This is good to test rewrite order complexity.
   The exact case study one will fail because we don't handle
   nested induction correctly yet. Here's a simple isolated
   case for a simpler version to see if the same problem shows up. *)

Theorem new10:
  forall a, a + S a = S (a + a).
Proof.
  intros a.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* The order we actually had in the case study *)
Theorem old10_v1:
  forall a, a + S (a + 0) = S (a + (a + 0)).
Proof.
  intros a.
  rewrite <- plus_n_O.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* Swapping the order of rewrites *)
Theorem old10_v2:
  forall a, a + S (a + 0) = S (a + (a + 0)).
Proof.
  intros a.
  rewrite -> plus_comm.
  rewrite <- plus_n_O.
  reflexivity.
Qed.


