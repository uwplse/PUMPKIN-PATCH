Require Import Coq.omega.Omega.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Require Import Patcher.Patch.

(* Super simple text of the Decide command: *)
Decide (forall x : Z, x - 1 < x) with (intros; omega) as proof.

(* Some observations:
 *   1. Some tactics, like Omega, need all hypotheses to be introduced before
 *      invocation.
 *   2. The robustness of the internal representation of a tactic script is.
 *      In particular, does it close over the tactic environment?
 *)
