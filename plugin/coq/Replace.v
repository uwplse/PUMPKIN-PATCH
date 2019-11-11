Add LoadPath "coq".
Require Import Patcher.Patch.

(*
 * This is an extremely example showing how
 * we can replace convertible subterms.
 *)

Definition add_three_ugly n :=
  1 + 2 + n.

Replace Convertible 3 in add_three_ugly as add_three.
Print add_three.

(*
 * We should generate these at some point
 *)
Lemma add_three_not_broken :
  add_three_ugly = add_three.
Proof.
  reflexivity.
Qed.

Definition add_three_expected n :=
  3 + n.

(*
 * This proof should go through _with these specific tactics_
 *)
Lemma add_three_correct :
  add_three = add_three_expected.
Proof.
  unfold add_three, add_three_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.