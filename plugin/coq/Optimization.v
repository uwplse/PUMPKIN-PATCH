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

(*
 * Here we apply a lemma in the inductive case, but the lemma is a more general
 * version of what we need:
 *)
Theorem add_0_r_slow_2 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - apply Nat.add_comm.
Qed.

Optimize Proof Term add_0_r_slow_2 as add_0_r_2.

(*
 * PUMPKIN thus is able to extract the lemma and the right arguments,
 * even though they are different from the arguments used in the inductive case:
 *)
Theorem test_opt_4 :
  add_0_r_2 = fun (n : nat) => Nat.add_comm n 0.
Proof.
  reflexivity.
Qed.

(*
 * This version rewrites by commutativity instead of applying it:
 *)
Theorem add_0_r_slow_3 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - rewrite Nat.add_comm. reflexivity.
Qed.

Optimize Proof Term add_0_r_slow_3 as add_0_r_3.

(*
 * As-is, PUMPKIN can remove the induction over the nats:
 *)
Theorem test_opt_5_almost :
  add_0_r_3 = 
    fun n : nat => 
      eq_ind_r (fun n0 : nat => n0 = n) eq_refl (Nat.add_comm n 0).
Proof.
  reflexivity.
Qed.

(*
 * But it's still not smart enough to remove the rewrite:
 *)
Theorem test_opt_5 :
  add_0_r_3 = 
    fun n : nat => Nat.add_comm n 0.
Proof.
  Fail reflexivity.
Admitted.

(*
 * NOTE: When PUMPKIN implements better handling of rewrites and is able to find
 * this patch, remove test_opt_5_almost and update test_opt_5 to pass.
 *)

(*
 * This version applies an extra induction cycle inline in the inductive case:
 *)
Theorem add_0_r_slow_4 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - induction n.
    + reflexivity.
    + simpl. rewrite <- IHn. reflexivity. 
Qed.

Optimize Proof Term add_0_r_slow_4 as add_0_r_4.

Definition add_0_r_4_expected (n : nat) : n + 0 = n :=
  nat_ind 
    (fun n0 : nat => n0 + 0 = n0) 
    eq_refl
    (fun (n0 : nat) (IHn : n0 + 0 = n0) =>
      eq_ind (n0 + 0) (fun n1 : nat => S (n0 + 0) = S n1) eq_refl n0 IHn)
    n.

(*
 * PUMPKIN is not good at rewrites and is also not good at nested induction,
 * so it does not find the most efficient proof:
 *)
Fail Theorem test_opt_6 : add_0_r_4 = add_0_r_4_expected.

(*
 * NOTE: When PUMPKIN implements better handling of rewrites and nested induction
 * and is able to find this patch, update test_opt_6 to pass.
 *)

(*
 * This is a minimal test for nested induction. It is defined as a term because 
 * it is a purposely minimal test case, but it's hard to get tactics to do this:
 *)
Definition add_0_r_slow_5 (n : nat) : n + 0 = n :=
  nat_ind 
    (fun n0 : nat => n0 + 0 = n0) 
    eq_refl
    (fun (n0 : nat) (IHn : n0 + 0 = n0) =>
      nat_ind 
        (fun n1 : nat => S n1 + 0 = S n1)
        eq_refl
        (fun (n1 : nat) (IHn1 : S n1 + 0 = S n1) =>
          eq_trans 
           (f_equal (fun f : nat -> nat => f (S (n1 + 0))) eq_refl) 
           (f_equal S IHn1)) 
        n0)
    n.

Optimize Proof Term add_0_r_slow_5 as add_0_r_5.

Definition add_0_r_5_expected (n : nat) : n + 0 = n :=
  nat_ind 
    (fun n0 : nat => n0 + 0 = n0) 
    eq_refl
    (fun (n0 : nat) (IHn : n0 + 0 = n0) =>
      eq_trans 
        (f_equal (fun f : nat -> nat => f (n0 + 0)) eq_refl) 
        (f_equal S IHn)) 
    n.

(*
 * PUMPKIN manages to find the most efficient proof, probably because
 * there are no inductive hypotheses of the form A -> B.
 *
 * NOTE: Broken. Fix soon. Not crucial to release.
 *)
Fail Theorem test_opt_7 : 
   add_0_r_5 = add_0_r_5_expected.
(*Proof.
  reflexivity.
Qed.*)

(*
 * With Preprocess, we can remove the extra fixpoint too:
 *)
Fixpoint add_0_r_slow_6 (n : nat) : n + 0 = n :=
  match n with
  | 0 => eq_refl
  | S n1 =>
      (fix F0 (n2 : nat) : S (n2 + 0) = S n2 :=
         match n2 with
         | 0 => eq_refl
         | S n3 => 
             eq_trans 
               (f_equal (fun f : nat -> nat => f (S (n3 + 0))) eq_refl) 
               (f_equal S (F0 n3))
         end) n1
  end.

Preprocess add_0_r_slow_6 as add_0_r_slow_6'.
Optimize Proof Term add_0_r_slow_6' as add_0_r_6.

(*
 * This gives us the same result:
 *
 * NOTE: Broken. Fix soon. Not crucial to release.
 *)
Fail Theorem test_opt_8 : 
   add_0_r_6 = add_0_r_5_expected.
(*Proof.
  reflexivity.
Qed.*)

(* --- Functions (doesn't work yet) --- *)

(*
 * We can also implement some functions inefficiently.
 * Let's see how this behaves. (We don't define the fixpoint
 * version because we have problems with A -> B hypotheses, still).
 *)
Program Definition slow_add : nat -> nat -> nat.
Proof.
  intros n m. induction n.
  - apply m.
  - apply S. induction IHn.
    + apply 0.
    + apply S. apply IHIHn.
Defined.

Optimize Proof Term slow_add as not_add.
Print not_add.

Eval compute in (not_add 4 7). (* 8 *)
Eval compute in (not_add 0 0). (* 1 *)
Eval compute in (not_add 0 1). (* 2 *)
Eval compute in (not_add 1 1). (* 2 *)

(*
 * As you can see, it doesn't work for functions as-is.
 * So we need to be careful about when we do this.
 * To work for functions, we need to be smarter about when we accept a result.
 * The result of the "optimization" is just the successor of m right now.
 *)

