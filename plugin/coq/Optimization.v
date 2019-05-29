Require Import Patcher.Patch.
Require Import Arith PeanoNat.

(*
 * PUMPKIN PATCH can remove extra induction principles and fixpoints.
 * The key is that proof optimization of this kind is simply patching against
 * the proof of "nothing" with the same structure. So optimization
 * is defined in terms of patching with a few parameter tweaks.
 *
 * Optimization is only as good as patching, and patching still has
 * limited functionality. For now, we show a few proofs we can do as-is.
 * The cases that fail should eventually pass; we mark those as Fail.
 * Optimization will continue to improve automatically as patching improves;
 * at that point, some of these tests will fail to Fail. If that happens,
 * we should remove the Fail command so that they pass.
 *)

(* --- A really simple toy example proof --- *)

(*
 * This is an inefficient proof of reflexivity with extra induction:
 *)
Theorem refl_slow :
  forall (n : nat),
    n = n.
Proof.
  intros. induction n; auto.
Qed.

Optimize Proof Term refl_slow as refl.

(*.
 * Optimizing this proof removes induction and produces a proof of refl:
 *)
Theorem test_opt_1 : 
  refl = fun (n : nat) => eq_refl. 
Proof. 
  reflexivity. 
Qed.

(* --- Pattern matching --- *)

(*
 * We can optimize proofs with pattern matching using the preprocess command:
 *)
Definition refl_slow_match (n : nat) : n = n :=
  match n with
  | 0 => eq_refl
  | S n1 => eq_refl
  end.

Preprocess refl_slow_match as refl_slow'.
Optimize Proof Term refl_slow' as refl'.

(*.
 * Optimizing this proof removes pattern matching and produces a proof of refl:
 *)
Theorem test_opt_2 : 
  refl' = fun (n : nat) => eq_refl. 
Proof. 
  reflexivity. 
Qed.

(* --- Variations on a theme --- *)

(*
 * These are various inefficient versions of add_0_r. Some of these work as-is,
 * some currently fail.
 *)

(*
 * Here we apply a lemma in the inductive case, but the lemma is exactly
 * the proof we want:
 *)
Theorem add_0_r_slow_1 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - apply Nat.add_0_r.
Qed.

Optimize Proof Term add_0_r_slow_1 as add_0_r_1.

(*
 * PUMPKIN thus is able to extract the lemma:
 *)
Theorem test_opt_3 :
  add_0_r_1 = fun (n : nat) => Nat.add_0_r n.
Proof.
  reflexivity.
Qed.

(* TODO using the IH *)
(* TODO fixpoint version *)
(* TODO things other than nats *)

(* --- TODO won't work yet; clean and merge simple version, then add issue for later; need to be smart about this --- *)

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
(* TODO just note that this doesn't work yet. Not smart enough for the nested induction. *)

(* --- TODO explain --- *)

(*
 * Let's start with a deliberately easy proof (haha still needs nested induction support).
 * Here's a version of add_0_r that does extra induction.
 * This one applies a lemma to get around lack of support for nested induction.
 *)
Theorem old3 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - rewrite <- Nat.add_comm. reflexivity.
Qed.
Print old3.
Optimize Proof Term old3 as new3.
Print new3. (* TODO test (this one does work) *)
(* TODO can we get it to be smart enough to remove the rewrite too? *)

Theorem old4 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. apply Nat.add_comm.
Qed.

Print old4.

Theorem old5 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Print old5.

Check (fun (n0 : nat) (IHn : n0 + 0 = n0) =>
   eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl IHn).

Check (fun (n0 : nat) (IHn : n0 + 0 = n0) =>
   eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl IHn).

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