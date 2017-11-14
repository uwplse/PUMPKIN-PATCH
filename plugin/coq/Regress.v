Add LoadPath "coq".
Require Import Example.
Require Import Identity.
Require Import Patcher.Patch.
Require Import Arith NPeano List.
Require Import Reverse.

(* For now, this checks literal equality with the expected patch.
   Later, we should just check if it is direct and if it completes the proof we want. *)

(* Identity *)

Patch Proof oldID newID as patchID.

Theorem testPatchID1 :
  patchID oldID = newID.
Proof.
  reflexivity.
Qed.

Theorem testPatchID2 :
  patchID newID = oldID.
Proof.
  reflexivity.
Qed.

(* 1 *)

Patch Proof old1 new1 as patch1.

Definition expectedPatch1 :=
  fun (n m p : nat) (_ : n <= m) (_ : m <= p) =>
    (fun (H1 : nat) (H2 : (fun p0 : nat => n <= p0) H1) =>
      le_plus_trans n H1 1 H2) p.

Theorem testPatch1 :
  patch1 = expectedPatch1.
Proof.
  reflexivity.
Qed.

(* 2 *)

Patch Proof old2 new2 as patch2.

Definition expectedPatch2 :=
  fun (n m p : nat) (_ : n <= m) (_ : m <= p) =>
    (fun (H1 : nat) (H2 : (fun p0 : nat => n <= p0) H1) =>
       le_S n H1 H2) p.

Theorem testPatch2 :
  patch2 = expectedPatch2.
Proof.
  reflexivity.
Qed.

(* 3 *)

Patch Proof old3 new3 as patch3.

Definition expectedPatch3 :=
  fun (n m p : nat) (_ : n <= m) (_ : m <= p) =>
    (fun (H1 : nat) (H2 : (fun p0 : nat => n <= p0) H1) =>
       le_lt_n_Sm n H1 H2) p.

Theorem testPatch3 :
  patch3 = expectedPatch3.
Proof.
  reflexivity.
Qed.

(* 4 *)

Patch Proof old4 new4 as patch4.

Definition expectedPatch4 :=
  fun (n m p : nat) (_ : n <= m) (_ : m <= p) =>
    (fun (H1 : nat) (H2 : (fun p0 : nat => n < S p0) H1) =>
      eq_ind_r (fun n0 : nat => n < n0) H2 (PeanoNat.Nat.add_comm H1 1)) p.

Theorem testPatch4 :
  patch4 = expectedPatch4.
Proof.
  reflexivity.
Qed.

(* 5 *)

Patch Proof old5 new5 as patch5.

Definition expectedPatch5 :=
  fun (n m : nat) (l1 l2 : list nat) (_ : ListSum l1 n) (_ _ : ListSum (l1 ++ l2) (n + m)) (H2 : ListSum (nil ++ l2) (0 + m)) =>
    eq_rec_r (fun l : list nat => ListSum l m) H2 (rev_involutive l2).

Theorem testPatch5 :
  patch5 = expectedPatch5.
Proof.
  reflexivity.
Qed.

(* 6 *)

Patch Proof old6 new6 as patch6.

Definition expectedPatch6 :=
  fun l1 l2 : list nat =>
    (fun (H : list nat) (H0 : (fun l3 : list nat => length (l3 ++ l2) = length l3 + length l2) H) =>
       eq_ind_r (fun n : nat => n = length (rev H) + length (rev l2))
         (eq_ind_r (fun n : nat => length (H ++ l2) = n + length (rev l2))
           (eq_ind_r (fun n : nat => length (H ++ l2) = length H + n) H0
              (rev_length l2))
           (rev_length H))
         (rev_length (H ++ l2)))
    l1.

Theorem testPatch6 :
  patch6 = expectedPatch6.
Proof.
  reflexivity.
Qed.

(* 7 *)

Patch Proof old7 new7 as patch7.

Definition expectedPatch7 :=
  fun (A B : Type) (f : A -> B) (l : list A) (x : A) (H : In x l -> In (f x) (map f l)) =>
    Morphisms.Reflexive_partial_app_morphism
      (Morphisms.subrelation_proper Morphisms_Prop.iff_iff_iff_impl_morphism tt
        (Morphisms.subrelation_respectful (Morphisms.subrelation_refl iff)
          (Morphisms.subrelation_respectful (Morphisms.subrelation_refl iff)
             Morphisms.iff_flip_impl_subrelation)))
       (Morphisms.reflexive_proper_proxy RelationClasses.iff_Reflexive (In x l))
    (In (f x) (rev (map f l))) (In (f x) (map f l))
    (RelationClasses.symmetry (in_rev (map f l) (f x))) H.

Theorem testPatch7 :
  patch7 = expectedPatch7.
Proof.
  reflexivity.
Qed.

(* 8 *)

Patch Proof old8 new8 as patch8.

Definition expectedPatch8 (n m n0 : nat) (_ : m = n) (H : n <= Init.Nat.max n0 m) :=
  le_plus_trans n (Init.Nat.max n0 m) (S O) H.

Theorem testPatch8 :
  patch8 = expectedPatch8.
Proof.
  reflexivity.
Qed.

(* --------------------- *)

