Add LoadPath "coq".
Require Import Patcher.Patch.
Require Import Regress.
Require Import Arith NPeano.

(* Regression tests for abstraction top-level. *)

Abstract patch4 to (forall (P : nat -> Prop) (n m p : nat), n <= m -> m <= p -> P (S p) -> P (p + 1)) as patch4_abs.

(* TODO test *)

Print patch4_abs.