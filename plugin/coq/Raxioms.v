Require Export ZArith_base.
Require Export Rdefinitions.
Local Open Scope R_scope.

Fixpoint INR (n:nat) : R :=
   match n with
   | O => 0
   | S O => 1
   | S n => INR n + 1
   end.

Arguments INR n%nat.

Fixpoint IPR_2 (p:positive) : R :=
  match p with
  | xH => 1 + 1
  | xO p => (1 + 1) * IPR_2 p
  | xI p => (1 + 1) * (1 + IPR_2 p)
  end.

Definition IPR (p:positive) : R :=
  match p with
  | xH => 1
  | xO p => IPR_2 p
  | xI p => 1 + IPR_2 p
  end.

Definition IZR' (z:Z) : R :=
  match z with
  | Z0 => 0
  | Zpos n => IPR n
  | Zneg n => - IPR n
  end.

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Export Rtrigo_fun.
Require Export Rtrigo_def.
Require Export Rtrigo_alt.
Require Export Cos_rel.
Require Export Cos_plus.
Require Import ZArith_base.
Require Import Zcomplements.
Require Import Fourier.
Require Import Ranalysis1.
Require Import Rsqrt_def.
Require Import PSeries_reg.

Lemma INR_IPR : forall p, INR (Pos.to_nat p) = IPR p.
Proof.
  assert (H: forall p, 2 * INR (Pos.to_nat p) = IPR_2 p).
    induction p as [p|p|] ; simpl IPR_2.
    rewrite Pos2Nat.inj_xI, S_INR, mult_INR, <- IHp.
    now rewrite (Rplus_comm (2 * _)).
    now rewrite Pos2Nat.inj_xO, mult_INR, <- IHp.
    apply Rmult_1_r.
  induction p as [p|p|]; unfold IPR.
  rewrite Pos2Nat.inj_xI, S_INR, mult_INR, <- H.
  apply Rplus_comm.
  now rewrite Pos2Nat.inj_xO, mult_INR, <- H.
  easy.
Qed.

Print INR_IPR.

 Lemma INR_IZR_INZ : forall n:nat, INR n = IZR (Z.of_nat n).
 Proof.
  simple induction n; auto with real.
  intros; simpl; rewrite SuccNat2Pos.id_succ;
    auto with real.
 Qed.

(* TODO above is minimally adapted *)

Lemma INR_IZR_INZ' : forall n:nat, INR n = IZR' (Z.of_nat n).
 Proof.
  simple induction n; intros.
  easy.
  simpl Z.of_nat. unfold IZR'.
  now rewrite <- INR_IPR, SuccNat2Pos.id_succ.
 Qed.

Require Import Patcher.Patch.
Patch Proof INR_IZR_INZ INR_IZR_INZ' as patch.
Print patch.

