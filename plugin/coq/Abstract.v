Add LoadPath "coq".
Require Import Patcher.Patch.
Require Import Regress.
Require Import Arith NPeano.

(* Regression tests for abstraction top-level. *)

(* --- Function Abstraction --- *)

Definition expected_abs_1 :=
  forall (P : nat -> Prop) (n m p : nat),
    n <= m ->
    m <= p ->
    P (S p) ->
    P (p + 1).

Abstract patch4 to expected_abs_1 as actual_abs_1.

Theorem test_abs_1 :
  expected_abs_1.
Proof.
  exact actual_abs_1.
Qed.

(* --- Argument Abstraction --- *)

(*
 * For now, this only handles really obvious cases
 *)

Definition expected_abs_2 :=
  forall (n0 n p : nat),
    ((fun m0 => n <= m0) n0) ->
    ((fun m0 => n <= m0 + 1) n0).

Definition patch_abs_2 n p (H : (fun m0 => n <= m0) p) :=
  le_plus_trans n p 1 H.

Abstract patch_abs_2 to expected_abs_2 as actual_abs_2.

Theorem test_abs_2 :
  expected_abs_2.
Proof.
  exact actual_abs_2.
Qed.

Definition expected_abs_3 :=
  forall (n0 n p : nat),
    ((fun m0 => n <= p) n0) ->
    ((fun m0 => n <= p + m0) n0).

Definition patch_abs_3 n p (H : (fun m0 => n <= p) 1) :=
  le_plus_trans n p 1 H.

Abstract patch_abs_3 to expected_abs_3 as actual_abs_3.

Theorem test_abs_3 :
  expected_abs_3.
Proof.
  exact actual_abs_3.
Qed.

