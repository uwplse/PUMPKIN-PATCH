(* Case study for porting a library from one Coq definition to another *)
(* Original problems are from Software Foundations (Inductive.v), solutions are from students *)
(* Cleaned up for easy write-up, got rid of extraneous things, but mostly the original proofs *)

Require Import Patcher.Patch.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(** **** Exercise: 3 stars (binary)  *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers.

    (Hint: Recall that the definition of [nat] above,

         Inductive nat : Type := | O : nat | S : nat -> nat.

    says nothing about what [O] and [S] "mean."  It just says "[O] is
    in the set called [nat], and if [n] is in the set then so is [S
    n]."  The interpretation of [O] as zero and [S] as successor/plus
    one comes from the way that we _use_ [nat] values, by writing
    functions to do things with them, proving things about them, and
    so on.  Your definition of [bin] should be correspondingly simple;
    it is the functions you will write next that will give it
    mathematical meaning.)

    (b) Next, write an increment function [incr] for binary numbers,
        and a function [bin_to_nat] to convert binary numbers to unary
        numbers.

    (c) Write five unit tests [test_bin_incr1], [test_bin_incr2], etc.
        for your increment and binary-to-unary functions.  (A "unit
        test" in Coq is a specific [Example] that can be proved with
        just [reflexivity], as we've done for several of our
        definitions.)  Notice that incrementing a binary number and
        then converting it to unary should yield the same result as
        first converting it to unary and then incrementing. *)

(* Talia: From ghostfs, but common auxiliary lemmas *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction m as [| m'].
  - simpl. rewrite -> plus_0_r. reflexivity.
  - simpl. rewrite <- IHm'. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* Talia: From marshall's, but really they are the same so just define a common one *)
Inductive bin : Type :=
  | B0  : bin
  | B2  : bin -> bin
  | B21 : bin -> bin.

Fixpoint incr (n : bin) : bin :=
  match n with
  | B0     => B21 B0
  | B2 n'  => B21 n'
  | B21 n' => B2 (incr n')
  end.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0    => B0
  | S n' => incr (nat_to_bin n')
  end.

Fixpoint normalize (b:bin) : bin :=
  match b with
    | B0 => B0
    | B2 b' => match normalize b' with
                | B0 => B0
                | b'' => B2 b''
              end
    | B21 b' => B21 (normalize b')
  end.

(* Talia: https://github.com/marshall-lee/software_foundations/commit/4c4c4962ad1c56ab7f97b9aedf708f4ac97e7c5a *)
Module marshall.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | B0     => O
  | B2 n'  => (bin_to_nat n') + (bin_to_nat n')
  | B21 n' => S ((bin_to_nat n') + (bin_to_nat n'))
  end.

End marshall.

(* https://github.com/blindFS/Software-Foundations-Solutions/blob/master/Basics.v *)

Module blindFS.

Fixpoint bin_to_nat (b: bin) : nat :=
  match b with
    | B0 => O
    | B2 b' => 2 * (bin_to_nat b')
    | B21 b' => 1 + 2 * (bin_to_nat b')
  end.

End blindFS.

Module marshall_induction.

Definition bin_to_nat := marshall.bin_to_nat.

Lemma S_S_plus : forall a b : nat,
  S a + S b = S (S (a + b)).
Proof.
  intros a b.
  induction a.
  reflexivity.
  simpl. rewrite <- IHa. reflexivity. Qed.

(* Talia: Original is below *)
Theorem bin_to_nat_pres_incr_original : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    rewrite -> S_S_plus.
    reflexivity.
Qed.

(* Talia: But for now, we only support one format as a proof of concept: *)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    assert (H : forall a b : nat, S a + S b = S (S (a + b))).
    + intros a b. apply S_S_plus.
    + rewrite -> H.
      reflexivity.
Qed.

(** [] *)

Theorem bin_to_nat_nat_to_bin : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n'].
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    reflexivity.
Qed.

End marshall_induction.

Module blindfs_induction.

Definition bin_to_nat := blindFS.bin_to_nat.

(* Talia: Original, but with indentation. *)
Theorem bin_to_nat_pres_incr : forall n : bin,
  bin_to_nat (incr n) = 1 + bin_to_nat n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    simpl.
    assert (H : forall a :nat, S (a + S (a + 0)) = S (S (a + (a + 0)))).
    + intros a.
      rewrite <- plus_n_O.
      rewrite -> plus_comm.
      induction a.
      * reflexivity.
      * simpl. reflexivity.
    + rewrite -> H.
      reflexivity.
Qed.

Theorem double_convertion : forall n:nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite -> bin_to_nat_pres_incr.
  rewrite -> IHn.
  reflexivity.
Qed.

Theorem normalize_again : forall b :bin, normalize (normalize b) = normalize b.
Proof.
  intros b.
  induction b as [| b' | b'].
  reflexivity.
  simpl.
  remember (normalize b') as n_b'.
  destruct n_b' as [| b'' | b''].
  reflexivity.
  replace (normalize (B2 (B2 b''))) with (match normalize (B2 b'') with | B0 => B0 | B2 c => B2 (B2 c) | B21 c => B2 (B21 c) end).
  rewrite -> IHb'. reflexivity.
  simpl. reflexivity.
  simpl. rewrite <- IHb'. reflexivity.
  simpl. rewrite -> IHb'. reflexivity.
Qed.

Theorem normalize_incr_comm : forall b : bin, normalize (incr b) = incr (normalize b).
Proof.
  intros b. induction b.
  reflexivity.
  simpl.
  remember (normalize b) as nb.
  destruct nb.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> IHb.
  remember (normalize b) as nb.
  destruct nb.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Theorem D_means_double : forall n:nat,
 nat_to_bin(n + n) = normalize(B2 (nat_to_bin n)).
Proof.
  intros n. induction n.
  reflexivity.
  replace (nat_to_bin (S n + S n)) with (incr (incr (nat_to_bin (n + n)))).
  rewrite -> IHn. rewrite <- normalize_incr_comm.
  rewrite <- normalize_incr_comm.
  simpl. reflexivity.
  simpl. rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Theorem normalize_correctness : forall b:bin,
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b.
  - reflexivity.
  - simpl. rewrite -> plus_0_r.
    rewrite -> D_means_double.
    simpl. rewrite -> IHb. rewrite -> normalize_again.
    reflexivity.
  - simpl. rewrite -> plus_0_r.
    rewrite -> D_means_double.
    rewrite -> IHb.
    simpl.
    rewrite -> normalize_again.
    remember (normalize b) as nb.
    destruct nb.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

End blindfs_induction.

(* Port blindFS to use Marshall's datatype *)

Module blindFS_induction_ported.

Definition bin_to_nat := marshall.bin_to_nat.

Theorem bin_to_nat_pres_incr : forall n : bin,
  bin_to_nat (incr n) = 1 + bin_to_nat n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    simpl.
    assert (H : forall a :nat, S (a + S a) = S (S (a + a))).
    + intros.
      rewrite -> plus_comm.
      induction a.
      * reflexivity.
      * simpl. reflexivity.
    + rewrite <- H. reflexivity.
Qed.

Definition cut :=
  forall (a : nat),
    S (a + S a) = S (S (a + a)) ->
    S (a + S (a + 0)) = S (S (a + (a + 0))).

(* Patch *)
Patch Proof blindfs_induction.bin_to_nat_pres_incr bin_to_nat_pres_incr cut by (fun (H : cut) b0 => H (bin_to_nat b0)) as patch.
Print patch.
Print patch_inv.

(* patch
   : forall (P : nat -> Prop) (b : bin),
     P (bin_to_nat b) -> P (bin_to_nat b + 0) *)

(* Talia: Now we have a patch in one direction. Let's invert it to get the other part of the isomorphism. *)

(* patch_inv =
fun (P : nat -> Prop) (b : bin) (H : P (bin_to_nat b + 0)) =>
eq_ind (bin_to_nat b + 0) P H (bin_to_nat b)
  (eq_sym (plus_n_O (bin_to_nat b)))
     : forall (P : nat -> Prop) (b : bin),
       P (bin_to_nat b + 0) -> P (bin_to_nat b) *)

(* Talia: Note that this is a common way to switch between types when one representation
   is more convenient for something. You prove an isomorphism between the two. Here we're
   just extracting the isomorphism from a change in an auxiliary lemma. *)

Theorem double_convertion : forall n:nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite -> bin_to_nat_pres_incr.
  rewrite -> IHn.
  reflexivity.
Qed.

Theorem normalize_again : forall b :bin, normalize (normalize b) = normalize b.
Proof.
  intros b.
  induction b as [| b' | b'].
  reflexivity.
  simpl.
  remember (normalize b') as n_b'.
  destruct n_b' as [| b'' | b''].
  reflexivity.
  replace (normalize (B2 (B2 b''))) with (match normalize (B2 b'') with | B0 => B0 | B2 c => B2 (B2 c) | B21 c => B2 (B21 c) end).
  rewrite -> IHb'. reflexivity.
  simpl. reflexivity.
  simpl. rewrite <- IHb'. reflexivity.
  simpl. rewrite -> IHb'. reflexivity.
Qed.

Theorem normalize_incr_comm : forall b : bin, normalize (incr b) = incr (normalize b).
Proof.
  intros b. induction b.
  reflexivity.
  simpl.
  remember (normalize b) as nb.
  destruct nb.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> IHb.
  remember (normalize b) as nb.
  destruct nb.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Theorem D_means_double : forall n:nat,
 nat_to_bin(n + n) = normalize(B2 (nat_to_bin n)).
Proof.
  intros n. induction n.
  reflexivity.
  replace (nat_to_bin (S n + S n)) with (incr (incr (nat_to_bin (n + n)))).
  rewrite -> IHn. rewrite <- normalize_incr_comm.
  rewrite <- normalize_incr_comm.
  simpl. reflexivity.
  simpl. rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Theorem normalize_correctness : forall b:bin,
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b.
  - reflexivity.
  - simpl. apply patch_inv. rewrite -> plus_0_r.
    rewrite -> D_means_double.
    simpl. rewrite -> IHb. rewrite -> normalize_again.
    reflexivity.
  - simpl. apply patch_inv. rewrite -> plus_0_r.
    rewrite -> D_means_double.
    rewrite -> IHb.
    simpl.
    rewrite -> normalize_again.
    remember (normalize b) as nb.
    destruct nb.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

(* Talia: Note that we've applied the patch in two places. *)
(* Not yet done: Adding this to hints [can't add it as-is] *)

(* Talia: One thing that's notable however is that it is applied to its inverse.
   The natural thing to do is to remove it altogether: *)

Theorem normalize_correctness_better : forall b:bin,
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b.
  - reflexivity.
  - simpl.
    rewrite -> D_means_double.
    simpl. rewrite -> IHb. rewrite -> normalize_again.
    reflexivity.
  - simpl.
    rewrite -> D_means_double.
    rewrite -> IHb.
    simpl.
    rewrite -> normalize_again.
    remember (normalize b) as nb.
    destruct nb.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

(* Talia: Since in fact we have switched to a definition that is easier to work with
   than the one we originally had. This is a common way to change definitions. *)

(* Talia: Just looking at tactics doesn't help us here since rewrite -> plus_0_r is used here
   instead of rewrite <- plus_n_0, even though the two produce equivalent terms (since they are inverses). *)

(* Talia: It would be good to do this automatically, but for now we can have the tool determine that patch_inv
   is applied to its own inverse. Let's see how that works: *)

(* Talia: The thing to do here [not yet implemented] is to call the path finding algorithm.
   Then, when the path is broken down, check for pairs that are each others inverses. Eliminate
   these pairs, and then fold the result. *)

(* Talia: Let's break that into a tactic first and see if it finds the pair. (Not yet done).
   Then we can make another tactic searches through the old term and finds applications of patch or
   patch_inv in its path. If it finds them, it tells you that you can remove them. (Not yet done).
   Alternatively, it can run on the new term, find the pair, and let you know that you can remove both
   of those functions. *)

(* These don't work yet because the factoring component doesn't yet support
   certain kinds of terms:
Factor normalize_correctness using prefix normalize.
Print normalize_0.
Print normalize_1. *)

End blindFS_induction_ported.

Module marshall_induction_ported.

Definition bin_to_nat := blindFS.bin_to_nat.

(* Talia: For now, our tactic only supports one format,
   with an explicitly cut lemma as a proof of concept *)

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    assert (forall a b : nat, S a + (S b + 0) = S (S (a + (b + 0)))).
    + intros.
      repeat rewrite <- plus_n_O.
      apply marshall_induction.S_S_plus.
    + rewrite -> H.
      reflexivity.
Qed.

(* Eventually, want this working with original *)
Theorem bin_to_nat_pres_incr_alt : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    repeat rewrite <- plus_n_O.
    rewrite -> marshall_induction.S_S_plus.
    reflexivity.
Qed.

(*
Print marshall_induction.bin_to_nat_pres_incr_original.
Print bin_to_nat_pres_incr_alt.
*)

Definition cut_alt :=
  forall (b : bin),
    S (bin_to_nat b) + S (bin_to_nat b) = S (S (bin_to_nat b + bin_to_nat b)) ->
    S (bin_to_nat b) + (S (bin_to_nat b) + 0) = S (S (bin_to_nat b + (bin_to_nat b + 0))).

(*  : forall b' : bin,
       S (bin_to_nat b') + S (bin_to_nat b') =
       S (S (bin_to_nat b' + bin_to_nat b')) *)

(* Talia: For now we expect a specific format *)
(* Talia: Then we can try patching that theorem: *)
Definition cut :=
  forall (a b : nat),
    S a + S b = S (S (a + b)) ->
    S a + S (b + 0) = S (S (a + (b + 0))).

Patch Proof marshall_induction.bin_to_nat_pres_incr bin_to_nat_pres_incr cut by (fun (H : cut) b => H (bin_to_nat b) (bin_to_nat b)) as patch.
Print patch.
Print patch_inv.

(* Talia: Now we have an isomorphism. *)

Theorem bin_to_nat_nat_to_bin : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n'].
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma nat_to_bin_Sn_plus_n : forall n : nat,
  nat_to_bin (S n + n) = B21 (nat_to_bin n).
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite -> plus_comm.
  rewrite -> IHn.
  reflexivity.
Qed.

Lemma nat_to_bin_n_plus_Sn : forall n : nat,
  nat_to_bin (n + S n) = B21 (nat_to_bin n).
Proof.
  intros n.
  rewrite -> plus_comm.
  rewrite -> nat_to_bin_Sn_plus_n.
  reflexivity.
Qed.

Lemma nat_to_bin_Sn_Sn : forall n : nat,
  nat_to_bin (S n + S n) = B2 (incr (nat_to_bin n)).
Proof.
  intros n.
  simpl.
  rewrite -> nat_to_bin_n_plus_Sn.
  simpl.
  reflexivity.
Qed.

(* Talia: In this case, the type got more complex for some of these theorems, so we actually do need
   the patch and it doesn't lead to an identity term.
   This shows up in a very straightforward way for this lemma. *)

Theorem bin_to_nat_plus : forall b : bin,
  (bin_to_nat b) + (bin_to_nat b) = bin_to_nat (B2 b).
Proof.
  intros b.
  destruct b as [|b'|b'].
  - reflexivity.
  - simpl. apply patch. auto.
  - simpl. apply patch. auto.
Qed.

(* Talia: And again here. *)

Theorem nat_to_bin_bin_to_nat : forall b : bin,
  nat_to_bin(bin_to_nat(b)) = normalize b.
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - simpl.
    rewrite <- IHb'.
    apply patch_inv.
    destruct (bin_to_nat b').
    + reflexivity.
    + rewrite -> nat_to_bin_Sn_Sn.
      simpl.
      destruct (nat_to_bin n) as [|b''|b''].
      * reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
  - simpl.
    rewrite <- IHb'.
    apply patch_inv.
    destruct (bin_to_nat b') as [|n].
    + reflexivity.
    + rewrite -> nat_to_bin_Sn_Sn.
      simpl. reflexivity.
Qed.

End marshall_induction_ported.
