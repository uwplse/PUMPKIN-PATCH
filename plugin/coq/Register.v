Require Import Coq.omega.Omega.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Require Import Patcher.Patch.

Register Patch Tactic (intros; omega) as omega for Z Z.lt Z.gt Z.le Z.ge (@eq Z).
Decide (forall n : Z, n >= 0 -> n + 2 >= 0) as test.
(*Unregister Patch Tactic omega.*)
