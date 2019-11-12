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

(*
 * This is silly, but a toy example for whole-module replacement.
 *)
Module Ugly.

  Definition add_three n :=
    1 + 2 + n.

  Definition add_four n :=
    S (add_three n).

  Inductive is_one (n : nat) :=
  | silly_constr : add_four n = 5 -> is_one n.

  Lemma is_one_correct :
    forall (n : nat), is_one n <-> n = 1.
  Proof.
   intros. split; intros.
   - induction H. inversion e. auto.
   - apply silly_constr. rewrite H. auto.
  Qed.

End Ugly.

Replace Convertible Module 3 in Ugly as Pretty.

Print Pretty.add_three.
Print Pretty.add_four.
Print Pretty.is_one.
Print Pretty.is_one_correct.

Lemma pretty_add_three_not_broken :
  Ugly.add_three = Pretty.add_three.
Proof.
  reflexivity.
Qed.

Lemma pretty_add_four_not_broken :
  Ugly.add_four = Pretty.add_four.
Proof.
  reflexivity.
Qed.

Print Ugly.is_one.
Print Pretty.is_one.

(*
 * NOTE: I think because of the way that equality works in Coq, with inductive
 * types, we can no longer use definitional equality the way we can with
 * functions. An unfortunate (or cool, depending on your perspective) consequence 
 * of this is that to even state correctness of a refactoring in Coq, we would
 * need to use equivalence up to transport, probably! Oy gevalt; everything is 
 * transport.
 *
 * We should generate the equivalence proofs, at least. Should be easy.
 *)
Program Definition pretty_is_one_not_broken_f :
  forall n, Ugly.is_one n -> Pretty.is_one n.
Proof.
  intros. induction H; constructor; auto. 
Defined.

Program Definition pretty_is_one_not_broken_f_inv :
  forall n, Pretty.is_one n -> Ugly.is_one n.
Proof.
  intros. induction H; constructor; auto. 
Defined.

Lemma pretty_is_one_not_broken_section :
  forall (n : nat) (H : Ugly.is_one n),
    pretty_is_one_not_broken_f_inv n (pretty_is_one_not_broken_f n H) = H.
Proof.
  intros. induction H; auto.
Qed.

Lemma pretty_is_one_not_broken_retraction :
  forall (n : nat) (H : Pretty.is_one n),
    pretty_is_one_not_broken_f n (pretty_is_one_not_broken_f_inv n H) = H.
Proof.
  intros. induction H; auto.
Qed.

(*
 * I will have to think hard to even state a theorem about Pretty.is_one_correct
 * not being broken without importing something like Univalent Parametricity!
 *)

Definition pretty_add_three_expected n :=
  3 + n.

(*
 * This proof should go through _with these specific tactics_
 *)
Lemma pretty_add_three_correct :
  Pretty.add_three = pretty_add_three_expected.
Proof.
  unfold Pretty.add_three, pretty_add_three_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

Definition pretty_add_four_expected n :=
  S (Pretty.add_three n).

Lemma pretty_add_four_correct :
  Pretty.add_four = pretty_add_four_expected.
Proof.
  unfold Pretty.add_four, pretty_add_four_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

(*
 * At this point, I would run into the transport problem again in trying to state
 * these theorems.
 *)

(* NOTE: Unfortunately, for now, if you want support for pattern matching instead of
   induction, you must preprocess. WIP on supporting this directly. Will be
   much easier than supporting this directly in general in PUMPKIN PATCH.
   Note that Preprocess does NOT always preserve definitional equality
   even when Replace Convertible does! Thus, you will want direct support! *)
