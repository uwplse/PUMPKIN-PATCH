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
Theorem opt_old0 :
  forall (n : nat),
    n = n.
Proof.
  intros. induction n.
  - reflexivity.
  - reflexivity.
Qed.

Optimize Proof Term opt_old0 as new0.
Print new0. (* eliminate Set via nat and we're good *)

(* --- A toy example proof (TODO why does this work????) --- *)

(*
 * Let's start with a deliberately easy proof (haha still needs nested induction support).
 * Here's a version of add_0_r that does extra induction.
 * This one applies a lemma to get around lack of support for nested induction.
 *)
Theorem opt_old1 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n using nat_rect. (* see #14 *)
  - reflexivity.
  - apply Nat.add_0_r.
Qed.

(* TODO needs level 2, unfolding ... *)

Print opt_old1.
(*
opt_old1 = 
fun n : nat =>
nat_rect (fun n0 : nat => n0 + 0 = n0) eq_refl
  (fun (n0 : nat) (_ : n0 + 0 = n0) => Nat.add_0_r (S n0)) n
     : forall n : nat, n + 0 = n

Argument scope is [nat_scope]
nat_identity_level_1 = 
fun n : nat => nat_rect (fun _ : nat => nat) 0 (fun n IHn : nat => n) n
     : nat -> nat

*)  

(*
 * Now we search for a patch from nat_identity to opt_old1.
 *)
Patch Proof opt_old1 cheat_for_now as opt_patch1.
Print opt_patch1.
Print opt_old1.

(* --- TODO w/o a lemma --- *)

(*
 * Let's start with a deliberately easy proof (haha still needs nested induction support).
 * Here's a version of add_0_r that does extra induction.
 *)
Theorem opt_old2 :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros. induction n using nat_rect. (* see #14 *)
  - reflexivity.
  - induction n using nat_rect.
    + reflexivity.
    + simpl. rewrite <- IHn. reflexivity. 
Qed.

Patch Proof opt_old2 cheat_for_now as opt_patch2.
Print opt_patch2.

(* nah *)

(* does this work *)

Theorem cheat_for_now2:
  forall (n : nat),
    Set.
Proof.
  intros n. induction n using nat_rect.
  - apply nat.
  - induction n using nat_rect.
    + apply nat.
    + apply nat.
Qed. 

Patch Proof opt_old2 cheat_for_now2 as opt_patch2'.
Print opt_patch2'.

(* nah, needs nested induction since it's in inductive case *)

(* TODO for next time: OK so we need to edit the algorithm to just check
   if even without substituting we have the type we want just from hypo
   to conclusion in itself. then this proof can just be unit, and we apply to tt *)

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