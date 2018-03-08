Require Import List.
Require Import Coq.Program.Equality.
Require Import Patcher.Patch.

(*******************************************************************************)
(*******************************************************************************)
(* This file demonstrates _patch registration_ using a toy formalization of    *)
(* the simply typed lambda calculus. In particular, this development simulates *)
(* a scenario with the following two changes:                                  *)
(*   (a) Switching between open and closed substitution                        *)
(*   (b) Refactoring the conclusion of a termination theorem                   *)
(*   (c) Using ornamentation to port lemmas from syntax with type annotations  *)
(*       to syntax without type annotations                                    *)
(*                                                                             *)
(* The formalization of syntax and typing for the lambda calculus is in the    *)
(* companion source file "Lambda.v". The specifics of that module are not      *)
(* important for following and understanding the main tutorial. The source     *)
(* below gives an operational semantics and interpreter implementation for the *)
(* call-by-value evaluation strategy.                                          *)
(*******************************************************************************)
(*******************************************************************************)

Require Import Lambda.

(* Operational semantics *)
Inductive step : expr -> expr -> Prop :=
| BetaAx e1 t e2 :
    value e2 ->
    step (App (Fun t e1) e2) (e1 <- e2)
| LeftCx e1 e1' e2 :
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
| RightCx e1 e2 e2' :
    value e1 -> step e2 e2' ->
    step (App e1 e2) (App e1 e2').
Notation "e1 --> e2" := (step e1 e2) (at level 40).

(* Reduction semantics: reflexive, transitive closure of operational semantics *)
Inductive reduces : expr -> expr -> Prop :=
| Refl e : reduces e e
| Step e1 e2 e3 : reduces e1 e2 -> step e2 e3 -> reduces e1 e3.
Notation "e1 ==> e2" := (reduces e1 e2) (at level 40).

(* Reduction semantics closed under left-stepping *)
Lemma reduces_left e1 e1' e2 :
  e1 ==> e1' -> App e1 e2 ==> App e1' e2.
Proof.
  intros H. induction H as [e1|e1 e1'' e1' Hreduces1 IH Hstep1]; try constructor.
  eapply Step. exact IH. apply LeftCx. assumption.
Qed.

(* Reduction semantics closed under right-stepping *)
Lemma reduces_right e1 e2 e2' :
  value e1 -> e2 ==> e2' -> App e1 e2 ==> App e1 e2'.
Proof.
  intros Hval H. induction H as [e2|e2 e2'' e2' Hreduces1 IH Hstep2]; try constructor.
  eapply Step. exact IH. apply RightCx; assumption.
Qed.

(* Reduction semantics transitive *)
Lemma reduces_trans e1 e2 e3 :
  e1 ==> e2 -> e2 ==> e3 -> e1 ==> e3.
Proof.
  intros Hreduces1 Hreduces2. induction Hreduces2; try assumption.
  eapply Step; (try apply IHHreduces2); assumption.
Qed.

Lemma progress : forall e t, typing nil e t -> (exists e', e --> e') \/ value e.
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

Lemma preservation : forall e e' t, typing nil e t -> e --> e' -> typing nil e' t.
Proof.
  intros e e' t H. revert e'. dependent induction H; intros e' Hstep.
  - inversion Hstep.
  - inversion Hstep; subst; try (apply AppTy with (t2 := t2); auto).
    inversion H; subst. apply (subst_typing e0 t1 nil nil e2 t2); auto.
Qed.

Fixpoint eval (n : nat) (e : expr) {struct n} : expr :=
  match n, e with
  | S n, App e1 e2 =>
    match eval n e1, eval n e2 with
    | Fun t1 e1', Fun t2 e2' =>
      eval n (e1' <- Fun t2 e2')
    | Fun t1 e1', e2' =>
      App (Fun t1 e1') e2'
    | e1', _ => App e1' e2
    end
  | _, _ => e
  end.

(* Evaluation is sound w.r.t. the reduction semantics *)
Theorem eval_ok e e' n : eval n e = e' -> e ==> e'.
Proof.
  revert e e'.
  induction n as [|n IH]; simpl; intros e e' E; try (rewrite <- E; constructor).
  (* Case analysis on the expression *)
  destruct e as [i|e1|e1 e2]; try (rewrite <- E; constructor).
  (* Evaluation of an operator expression is sound *)
  destruct (eval n e1) as [i1|e11|e11 e12] eqn:He1; apply IH in He1;
    eapply reduces_trans;
    try (eapply reduces_left; exact He1);
    try (rewrite <- E; apply Refl).
  (* Evaluation of an operand expression is sound *)
  destruct (eval n e2) as [i2|e21|e21 e22] eqn:He2; apply IH in He2;
    eapply reduces_trans;
    try (eapply reduces_right; [constructor|exact He2]);
    try (rewrite <- E; apply Refl).
  (* Evaluation of a beta-redex is sound *)
  apply IH in E. eapply reduces_trans.
  - eapply Step. apply Refl. constructor. constructor.
  - assumption.
Qed.