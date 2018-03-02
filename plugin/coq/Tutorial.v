Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
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

(* Ground reduction rules (untyped beta) *)
Inductive rule : expr -> expr -> Prop :=
| Beta e1 t e2 : rule (App (Abs t e1) e2) (e1 <- e2).

(* Reduction steps (contextual lifting of rules) *)
Inductive step : expr -> expr -> Prop :=
| Context C e1 e2 : rule e1 e2 -> step (C[e1]) (C[e2]).
Notation "e1 --> e2" := (step e1 e2) (at level 40).

(* Reduction sequences *)
Inductive step_star : expr -> expr -> Prop :=
| Refl e : step_star e e
| Step e1 e2 e3 : step_star e1 e2 -> step e2 e3 -> step_star e1 e3.
Notation "e1 -->* e2" := (step_star e1 e2) (at level 40).

(* Continuation arising during recursive evaluation *)
Inductive cont : Set :=
| KRet : cont (* expression in top-level position *)
| KApp : expr -> cont -> cont. (* expression in application position *)

(* Reconstruct residual term from continuation *)
Fixpoint ret (e1 : expr) (k : cont) {struct k} : expr :=
  match k with
  | KApp e2 k0 => ret (App e1 e2) k0
  | KRet => e1
  end.

(* Top-level evaluation *)
Fixpoint eval (i : nat) (e : expr) (k : cont) {struct i} : expr :=
  match i with
  | S i =>
    match e with
    | Var _ => ret e k (* free variable, so done *)
    | App e1 e2 => eval i e1 (KApp e2 k)
    | Abs e1 =>
      match k with
      | KApp e2 k0 => eval i (e1 <- e2) k0
      | KRet => ret e k (* lambda vlue, so done *)
      end
    end
  | O => ret e k (* out of fuel, so done *)
  end.

End CallByName.

