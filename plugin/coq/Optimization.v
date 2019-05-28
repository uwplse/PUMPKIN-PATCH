Require Import Patcher.Patch.
Require Import Arith PeanoNat.

(*
 * PUMPKIN PATCH can remove extra induction principles and fixpoints.
 * The key is that proof optimization of this kind is simply patching against
 * identity, where identity is a formulaic proof that can be defined for each
 * induction principle. If PUMPKIN PATCH finds a patch, this is a more efficient
 * proof of the same theorem.
 *
 * We will soon have automation to construct this identity proof automatically.
 * For now, and to make it easier to build test cases later on, let's walk through
 * this manually.
 * 
 * TODO update above
 *)

(* --- A really really simple toy example proof --- *)

(*
 * TODO explain
 *)
Theorem old0 :
  forall (n : nat),
    n = n.
Proof.
  intros. induction n.
  - reflexivity.
  - reflexivity.
Qed.

Optimize Proof Term old0 as new0.
Print new0. (* TODO test *)

(* --- A toy example proof --- *)

(*
 * Let's start with a deliberately easy proof (haha still needs nested induction support).
 * Here's a version of add_0_r that does extra induction.
 * This one applies a lemma to get around lack of support for nested induction.
 *)
Theorem old1 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - apply Nat.add_0_r.
Qed.

Print old1.
Optimize Proof Term old1 as new1.
Print new1. (* TODO test *)

(* --- TODO w/o a lemma --- *)

(*
 * Let's start with a deliberately easy proof (haha still needs nested induction support).
 * Here's a version of add_0_r that does extra induction.
 *)
Theorem old2 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - induction n.
    + reflexivity.
    + simpl. rewrite <- IHn. reflexivity. 
Qed.

Optimize Proof Term old2 as new2.
Print new2. (* TODO test *)
Print opt_patch2.
(* --- TODO w/ a tactic --- *)

(* --- TODO a more realistic version --- *)


(* TODO a more realistic version *)

(* TODO fixpoint version *)

(*
 * Now, let's try something more complex, from the standard library.
 *)

(* TODO *)

(* --- Functions --- *)

(* TODO *)