Add LoadPath "coq".
Require Import Example.
Require Import Patcher.Patch.
Require Import Arith NPeano.
Require Import List.

(* new -> old *)

Patch Proof old4 new4 as patchForward1.

Definition expectedPatchForward1 :=
  fun (n m p : nat) (_ : n <= m) (_ : m <= p) =>
    (fun (H1 : nat) (H2 : (fun p0 : nat => n < S p0) H1) =>
      eq_ind_r (fun n0 : nat => n < n0) H2 (PeanoNat.Nat.add_comm H1 1)) p.

Theorem testPatchForward1 :
  patchForward1 = expectedPatchForward1.
Proof.
  reflexivity.
Qed.

(* old -> new *)

Patch Proof new4 old4 as patchBackward1.

Definition expectedPatchBackward1 :=
  fun (n m p : nat) (_ : n <= m) (_ : m <= p) (H2 : n < p + 1) =>
      eq_ind_r (fun n0 : nat => n < n0) H2 (eq_sym (PeanoNat.Nat.add_comm p 1)).

Theorem testPatchBackward1 :
  patchBackward1 = expectedPatchBackward1.
Proof.
  reflexivity.
Qed.

(* ---------- *)

Definition oldRev (n m : nat) :=
  eq_ind_r
    (fun n0 : nat => n < n0)
    (eq_ind
      (S n + m)
      (fun n0 : nat => n < n0)
      (lt_plus_trans
         n
         (S n)
         m
         (PeanoNat.Nat.lt_succ_diag_r n))
       (S (n + m))
       (PeanoNat.Nat.add_succ_l n m))
    (PeanoNat.Nat.add_succ_r n m).

Definition newRev (n m : nat) :=
  lt_plus_trans n (S n) m (PeanoNat.Nat.lt_succ_diag_r n).

(* new -> old *)

Definition expectedPatchForward2 := 
fun (n m : nat) (H : n < S n + m) =>
eq_ind_r (fun n0 : nat => n < n0)
  (eq_ind (S n + m) (fun n0 : nat => n < n0) H (S (n + m))
     (PeanoNat.Nat.add_succ_l n m)) (PeanoNat.Nat.add_succ_r n m).

Patch Proof oldRev newRev as patchForward2.

Theorem testPatchForward2 :
  patchForward2 = expectedPatchForward2.
Proof.
  reflexivity.
Qed.

(* old -> new *)

Definition expectedPatchBackward2 :=
fun (n m : nat) (H : n < n + S m) =>
eq_ind (S (n + m)) (fun n0 : nat => n < n0)
  (eq_ind_r (fun n0 : nat => n < n0) H (eq_sym (PeanoNat.Nat.add_succ_r n m)))
  (S n + m) (eq_sym (PeanoNat.Nat.add_succ_l n m)).

Patch Proof newRev oldRev as patchBackward2.

Theorem testPatchBackward2 :
  patchBackward2 = expectedPatchBackward2.
Proof.
  reflexivity.
Qed.

(* --- John's variants on behavior because of superfluous hypothesis --- *)

Definition patchForward3 (n m : nat) (H : n < S n + m) : n < n + S m := 
eq_ind_r (fun n0 : nat => n < n0)
  (eq_ind_r (fun n0 : nat => n < n0) H 
     (PeanoNat.Nat.add_succ_l n m)) (PeanoNat.Nat.add_succ_r n m).

Definition expectedPatchBackward3 (n m : nat) (H : n < n + S m) :=
eq_ind_r (fun n0 : nat => n < n0)
  (eq_ind_r (fun n0 : nat => n < n0) H (eq_sym (PeanoNat.Nat.add_succ_r n m)))
  (eq_sym (PeanoNat.Nat.add_succ_l n m)).

Invert patchForward3 as patchBackward3.

Theorem testPatchBackward3 :
  patchBackward3 = expectedPatchBackward3.
Proof.
  reflexivity.
Qed.

Definition patchForward4 (n m : nat) (H : n < S n + m) := 
eq_ind_r (fun n0 : nat => n < n0)
  H (PeanoNat.Nat.add_succ_r n m).

Definition expectedPatchBackward4 (n m : nat) (H : n < n + S m) :=
eq_ind_r (fun n0 : nat => n < n0) H (eq_sym (PeanoNat.Nat.add_succ_r n m)).

Invert patchForward4 as patchBackward4.

Theorem testPatchBackward4 :
  patchBackward4 = expectedPatchBackward4.
Proof.
  reflexivity.
Qed.