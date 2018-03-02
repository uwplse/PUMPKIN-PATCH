Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Patcher.Patch.

(*******************************************************************************)
(*******************************************************************************)
(* This file demonstrates using _patch registration_ on a toy formalization    *)
(* of the simply typed lambda calculus. In particular, this development        *)
(* simulates a scenario with the following two changes:                        *)
(*   (a) Switching from a call-by-name to normal-order evaluation strategy     *)
(*   (b) Refactoring the conclusion of a termination theorem                   *)
(*******************************************************************************)
(*******************************************************************************)

(*******************************************************************************)
(* The formalization is in the companion source file "Lambda.v". The exact     *)
(* details of the formalization are not important for understanding the        *)
(* tutorial; we use this library simply to illustrate the workflow of Pumpkin  *)
(* Patch on a concrete and realistic development project.                      *)
(*******************************************************************************)

Require Import Lambda.

(*******************************************************************************)
(* This module is our starting point. It implements a call-by-name reduction   *)
(* semantics and proves progress and preservation w.r.t. the type system.      *)
(*******************************************************************************)

Module CallByName.

(* Operational semantics *)
Inductive step : expr -> expr -> Prop :=
| Beta e1 t e2 : step (App (Fun t e1) e2) (e1 <- e2)
| Left e1 e1' e2 : step e1 e1' -> step (App e1 e2) (App e1' e2).
Notation "e1 --> e2" := (step e1 e2) (at level 40).

(* Reduction sequences *)
Inductive step_star : expr -> expr -> Prop :=
| Refl e : step_star e e
| Step e1 e2 e3 : step_star e1 e2 -> step e2 e3 -> step_star e1 e3.
Notation "e1 -->* e2" := (step_star e1 e2) (at level 40).

Theorem progress : forall e t, typing nil e t -> (exists e', step e e') \/ value e.
Proof.
  intros e t H. dependent induction H.
  - right. constructor.
  - left. destruct (IHtyping1 eq_refl) as [[e1' Hstep1]|Hvalue1]; clear IHtyping1.
    + exists (App e1' e2). constructor. assumption.
    + inversion Hvalue1 as [t0 e0 He1]. subst e1. exists (e0 <- e2). constructor.
Qed.

Lemma preservation : forall e e' t, typing nil e t -> step e e' -> typing nil e' t.
Proof.
  intros e e' t H. revert e'. dependent induction H; intros e' Hstep.
  - inversion Hstep.
  - inversion Hstep; subst. apply (subst_typing e0 t1 nil nil e2 t2); auto.
    inversion H; subst. assumption.
    apply TApp with (t2 := t2); try assumption. apply IHtyping1 with (e' := e1'); auto.
Qed.

Lemma progress' : forall e t, typing nil e t -> exists e', step e e' \/ value e.
Proof.
  intros e t Htyping. destruct (progress e t Htyping).
  - destruct H as [e'' step]. exists e''. left. assumption.
  - exists e. right. assumption.
Qed.

Lemma progress_patch : forall e, (exists e', step e e' \/ value e) -> (exists e', step e e') \/ value e.
Proof.
  intros e. destruct 1 as [e' H]. destruct H.
  - left. exists e'. assumption.
  - right. assumption.
Qed.

Register Patch Lemma progress_patch.

Inductive cont : Set :=
| KRet : cont
| KApp : expr -> cont -> cont.

Fixpoint rebuild (e1 : expr) (k : cont) : expr :=
  match k with
  | KApp e2 k => rebuild (App e1 e2) k
  | KRet => e1
  end.

Fixpoint eval (i : nat) (e : expr) (k : cont) {struct i} : expr * cont :=
  match i with
  | S i =>
    match e, k with
    | App e1 e2, _ => eval i e1 (KApp e2 k)
    | Fun _ e1, KApp e2 k => eval i (e1 <- e2) k
    | _, _ => (e, k)
    end
  | O => (e, k)
  end.

End CallByName.

(*******************************************************************************)
(* This module is our (desired) ending point. It implements a call-by-value    *)
(* reduction semantics and proves progress and preservation w.r.t. the type    *)
(* system. In the next step, we'll show how to generate the update lemmas      *)
(* from the previous module by patching.                                       *)
(*******************************************************************************)

Module CallByValue.

(* Operational semantics *)
Inductive step : expr -> expr -> Prop :=
| Beta e1 t e2 :
    value e2 ->
    step (App (Fun t e1) e2) (e1 <- e2)
| Left e1 e1' e2 :
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
| Right e1 e2 e2' :
    value e1 -> step e2 e2' ->
    step (App e1 e2) (App e1 e2').
Notation "e1 --> e2" := (step e1 e2) (at level 40).

(* Reduction sequences *)
Inductive step_star : expr -> expr -> Prop :=
| Refl e : step_star e e
| Step e1 e2 e3 : step_star e1 e2 -> step e2 e3 -> step_star e1 e3.
Notation "e1 -->* e2" := (step_star e1 e2) (at level 40).

Theorem progress : forall e t, typing nil e t -> (exists e', step e e') \/ value e.
Proof.
  intros e t H. dependent induction H.
  - right. constructor.
  - left. destruct (IHtyping1 eq_refl) as [[e1' Hstep1]|Hvalue1]; clear IHtyping1.
    + exists (App e1' e2). constructor. assumption.
    + destruct (IHtyping2 eq_refl) as [[e2' Hstep2]|Hvalue2]; clear IHtyping2.
      * exists (App e1 e2'). constructor; assumption.
      * inversion Hvalue1 as [t0 e0 He1]. subst e1.
        exists (e0 <- e2). constructor; assumption.
Qed.

Theorem preservation : forall e e' t, typing nil e t -> step e e' -> typing nil e' t.
Proof.
  intros e e' t H. revert e'. dependent induction H; intros e' Hstep.
  - inversion Hstep.
  - inversion Hstep; subst; try (apply TApp with (t2 := t2); auto).
    inversion H; subst. apply (subst_typing e0 t1 nil nil e2 t2); auto.
Qed.

Inductive cont : Set :=
| KRet : cont
| KApp : expr -> cont -> cont
| KArg : expr -> cont -> cont.

Fixpoint eval (i : nat) (e : expr) (k : cont) {struct i} : expr * cont :=
  match i with
  | S i =>
    match e, k with
    | App e1 e2, _ => eval i e2 (KArg e1 k)
    | Fun _ e1, KApp e2 k => eval i (e1 <- e2) k
    | e2, KArg e1 k => eval i e1 (KApp e2 k)
    | _, _ => (e, k)
    end
  | O => (e, k)
  end.

End CallByValue.

