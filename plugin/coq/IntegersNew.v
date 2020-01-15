(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* These are selected benchmarks from the CompCert Integers.v git history,
   minimized to what is relevant, and modified slightly to work with existing
   constructs.

   They test simple changes in constructors of inductive types,
   keeping theorem conclusions the same. *)

(** Formalizations of machine integers modulo $2^N$ #2<sup>N</sup>#. *)

Add LoadPath "coq".
Require Import Axioms.
Require Import CoqLib.
Require Import IntegersOld.
Require Import Patcher.Patch.

(** * Parameterization by the word size, in bits. *)

Module Type WORDSIZE.
  Variable wordsize: nat.
  Axiom wordsize_not_zero: wordsize <> 0%nat.
End WORDSIZE.

Module Make(WS: WORDSIZE).

Definition wordsize: nat := WS.wordsize.
Definition modulus : Z := two_power_nat wordsize.

(** * Representation of machine integers *)

(** A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded. *)

Record int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.

Definition int_ind :=
  fun (P : int -> Type) (f : forall (intval : Z) (intrange : -1 < intval < modulus),
  P {| intval := intval; intrange := intrange |}) (i : int) =>
  match i as i0 return (P i0) with
  | {| intval := x; intrange := x0 |} => f x x0
  end.

(** Binary decomposition of integers (type [Z]) *)

Definition Z_bin_decomp (x: Z) : bool * Z :=
  match x with
  | Z0 => (false, 0)
  | Zpos p =>
      match p with
      | xI q => (true, Zpos q)
      | xO q => (false, Zpos q)
      | xH => (true, 0)
      end
  | Zneg p =>
      match p with
      | xI q => (true, Zneg q - 1)
      | xO q => (false, Zneg q)
      | xH => (true, -1)
      end
  end.

Definition Z_bin_comp (b: bool) (x: Z) : Z :=
  if b then Zdouble_plus_one x else Zdouble x.

Lemma Z_bin_comp_eq:
  forall b x, Z_bin_comp b x = 2 * x + (if b then 1 else 0).
Proof.
  unfold Z_bin_comp; intros. destruct b.
  apply Zdouble_plus_one_mult.
  rewrite Zdouble_mult. omega.
Qed.

Lemma Z_bin_comp_decomp:
  forall x, Z_bin_comp (fst (Z_bin_decomp x)) (snd (Z_bin_decomp x)) = x.
Proof.
  destruct x; simpl.
  auto.
  destruct p; auto.
  destruct p; auto. simpl.
  rewrite <- Pplus_one_succ_r. rewrite Pdouble_minus_one_o_succ_eq_xI. auto.
Qed.

Lemma Z_bin_comp_decomp2:
  forall x b y, Z_bin_decomp x = (b, y) -> x = Z_bin_comp b y.
Proof.
  intros. rewrite <- (Z_bin_comp_decomp x). rewrite H; auto.
Qed.

(** Fast normalization modulo [2^n]. *)

Fixpoint Z_mod_two_p (x: Z) (n: nat) {struct n} : Z :=
  match n with
  | O => 0
  | S m => let (b, y) := Z_bin_decomp x in Z_bin_comp b (Z_mod_two_p y m)
  end.

Lemma Z_mod_two_p_range:
  forall n x, 0 <= Z_mod_two_p x n < two_power_nat n.
Proof.
  induction n; simpl; intros.
  rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. destruct (Z_bin_decomp x) as [b y] eqn:?. 
  rewrite Z_bin_comp_eq. generalize (IHn y). destruct b; omega.
Qed.

Lemma Z_mod_two_p_range':
  forall n x, -1 < Z_mod_two_p x n < two_power_nat n.
Proof.
  intros. generalize (Z_mod_two_p_range n x). abstract omega.
Qed.

Lemma Z_mod_two_p_eq:
  forall n x, Z_mod_two_p x n = Zmod x (two_power_nat n).
Proof.
 assert (forall n x, exists y, x = y * two_power_nat n + Z_mod_two_p x n).
    induction n; simpl; intros.
    rewrite two_power_nat_O. exists x. ring.
    rewrite two_power_nat_S.
    destruct (Z_bin_decomp x) as [b y] eqn:?.
    destruct (IHn y) as [z EQ]. 
    exists z. rewrite (Z_bin_comp_decomp2 _ _ _ Heqp). 
    repeat rewrite Z_bin_comp_eq. rewrite EQ at 1. ring.
  intros. 
  destruct (H n x) as [y EQ]. 
  symmetry. apply Zmod_unique with y. auto. apply Z_mod_two_p_range.
Qed.

(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed 
  respectively. *)

Definition unsigned (n: int) : Z := intval n.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition repr (x: Z) : int := 
  mkint (Z_mod_two_p x wordsize) (Z_mod_two_p_range' wordsize x).

Lemma mkint_eq:
  forall x y Px Py, x = y -> mkint x Px = mkint y Py.
Proof.
  intros. subst y. 
  generalize (proof_irr Px Py); intro.
  subst Py. reflexivity.
Qed.

(** * Properties of integers and integer arithmetic *)

(** ** Properties of the coercions between [Z] and [int] *)

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Proof.
  intros i. destruct i. simpl. abstract omega.
Qed.
Hint Resolve unsigned_range: ints.

(* Now get the patch from the changed proof *)
Module IntOld := IntegersOld.Make(WS).

Preprocess unsigned_range as unsigned_range_new.
Preprocess IntOld.unsigned_range as unsigned_range_old.
Patch Proof unsigned_range_old unsigned_range_new as patch.

Print patch.

(* Use the patch to prove repr_unsigned *)
Hint Resolve patch.

Theorem repr_unsigned:
  forall i, repr (unsigned i) = i.
Proof.
  intros i. destruct i; simpl; intros. unfold repr. apply mkint_eq.
  rewrite Z_mod_two_p_eq. apply Zmod_small; auto.
Qed.

Theorem repr_unsigned_tactic:
  forall i, repr (unsigned i) = i.
Proof.
  patch unsigned_range_old unsigned_range_new as p.
  intros i. destruct i; simpl; intros. unfold repr. apply mkint_eq.
  rewrite Z_mod_two_p_eq. apply Zmod_small. apply p. auto.
Qed.

Hint Resolve repr_unsigned : ints.

End Make.
