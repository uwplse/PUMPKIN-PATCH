Require Import Coq.omega.Omega.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Require Import Patcher.Patch.

Register Patch Tactic (intros; omega) as omega for Z Z.lt Z.gt Z.le Z.ge (@eq Z).

Decide (forall x : Z, x - 1 < x) with omega as proof.

Decide (forall x : Z, x - 1 < x) as proof'.
