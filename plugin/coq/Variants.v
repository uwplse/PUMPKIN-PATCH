Require Import Patcher.Patch.
Require Import Arith NPeano.
Require Import List.

(* Simple difference in inductive proofs, with different variants of each.

All of these are kinds of proofs the tool has support for so far,
using the most developed algorithm (differences in conclusions).
So they are differences in inductive proofs that induct over the same
type where the conclusion has changed. They only support one level of
induction, since we know we can't handle two yet, generally (we need
to improve IH elimination to account for that, or maybe break it down
into a sequence of lemmas that accounts for induction).

The variants are simple ways of changing the proofs to see how many
candidates the algorithm finds, whether it's successful at all,
what core components it uses, and whether just looking at the
difference in tactics would have been sufficient.

Also, we'll have some measure of theorem complexity at some point, too.
*)

(* Measures of complexity can be:

  For the difference in proofs:
  1. Was the patch inside or outside of the application of induction?
  2. Can a difference in tactics give you the answer?
  3. Did the proofs use any special tactics?

  For the theorems:
  1. How complex was the theorem itself? (Need to define, still)
  2. How complex was the inductive type itself? (Need to define, still)
*)

(* So far these variants look at differences in proofs, but nothing else yet *)

(* TODO test success, measure # candidates, complexity *)

Require Import Patcher.Patch.

Add LoadPath "coq".
Require Import Variants1.
Require Import Variants2.
Require Import Variants3.
Require Import Variants4.
Require Import Variants5.
Require Import Variants6.
Require Import Variants7.
Require Import Variants8.
Require Import Variants9.
Require Import Variants10.

(*
 * S: Success
 * F: Failure
 *)

(* Same style of proof [only change tactics if we need to] *)
(* Four variants on proof *)
(* Remove all redundant terms (control w/ same) *)
(* Remove non-inductive proofs (don't consider yet) *)
(* Just don't consider omega for now, note somewhere *)
(* Changes in hypotheses and omega are just unsupported features [omega only works if it's the full patch, can't abstract it] *)
(* Control for tool being proof-of-concept *)

Time Patch Proof old1_v1 new1 as patch1_v1. (* S *) (* 0 [no lifting] *)
Time Patch Proof old1_v2 new1 as patch1_v2. (* S *) (* 1 [lifting] *)
Time Patch Proof old1_v3 new1 as patch1_v3. (* S *) (* 0 [no lifting] *)
Time Patch Proof old1_v4 new1 as patch1_v4. (* S *) (* 1 [lifting] *)

Definition new2 := new1.

Time Patch Proof old2_v1 new2 as patch2_v1. (* S *) (* 0 [no lifting] *)
Time Patch Proof old2_v2 new2 as patch2_v2. (* S *) (* 1 [lifting] *)
Time Patch Proof old2_v3 new2 as patch2_v3. (* S *) (* 0 [no lifting] *)
Time Patch Proof old2_v4 new2 as patch2_v4. (* S *) (* 1 [lifting] *)

(* In this case, neither is stronger than the other, but also both
   are as strong as possible, so they must pass through the same
   intermediate lemma.

   This is a more complex theorem difference *)

Definition new3 := old1_v1.
Definition old3_v1 := old2_v1.
Definition old3_v2 := old2_v2.
Definition old3_v3 := old2_v3.
Definition old3_v4 := old2_v4.

Time Patch Proof old2_v1 new3 as patch3_v1. (* F *) (* 0 *)
Time Patch Proof old2_v2 new3 as patch3_v2. (* F *) (* 0 *)
Time Patch Proof old2_v3 new3 as patch3_v3. (* F *) (* 0 *)
Time Patch Proof old2_v4 new3 as patch3_v4. (* F *) (* 0 *)

(* What this demonstrates is that even though we can get from the stronger lemma to both of them,
   we don't know how to get between them. *)

(*
 * new1---->old2
 *   |
 *   |  ?
 *   V
 * old1
 *)

(* This happens even though it is in fact possible to get between the two, since the most efficient way to prove both is through new1 *)

(* In this case, neither is stronger than the other theorem statement,
   and both are as strong as possible. Also a more complex theorem difference.
   Here, one proof is more natural than the other, so one will take fewer candidates, but both directions could work in theory.
   Though in this case, with these proofs, there is no direct patch between the reverse two inverted, so that it fails is expected.
   Even if our inversion algorithm were better, this should still fail.
   The most efficient way to prove n < S p is via hypotheses, not via n <= p.
   See: how scary the proof of le_lt_pred is.
   Rewrites weren't possible here so you don't see those tests.
*)

Time Patch Proof old4_v1 new4 as patch4_v1. (* S *) (* 0 [no lifting] *)
Time Patch Proof old4_v2 new4 as patch4_v2. (* S *) (* 1 [lifting] *)

Time Patch Proof new4 old4_v1 as patch4_v1_rev. (* F *) (* 0 [no lifting, reversal] *)
Time Patch Proof new4 old4_v2 as patch4_v2_rev. (* F *) (* 4 [lifting, reversal] *)

(* Same situation, but this time, the patch is invertible. *)

Definition new7 := old4_v2.

Time Patch Proof old7_v1 new7 as patch7_v1. (* S *) (* 0 [no lifting] *)
Time Patch Proof old7_v2 new7 as patch7_v2. (* S *) (* 1 [lifting] *)

Time Patch Proof new7 old7_v1 as patch7_v1_rev. (* S *) (* 0 [no lifting, reversal] *)
Time Patch Proof new7 old7_v2 as patch7_v2_rev. (* S *) (* 1 [lifting, reversal] *)

(* These two are also equally strong with one more natural than the other, but in this case,
   since we pass through rewrites, our patches are invertible. Also, this inductive type
   is more complex. *)

Time Patch Proof old5_v1 new5 as patch5_v1. (* S *) (* 0 [no lifting] *)
Time Patch Proof old5_v2 new5 as patch5_v2. (* S *) (* 17 [lifting] *)

Time Patch Proof new5 old5_v1 as patch5_v1_rev. (* S *)(* 0 [no lifting, reversal] *)
Time Patch Proof new5 old5_v2 as patch5_v2_rev. (* S *) (* 17 [lifting, reversal] *)

(* More equally strong terms, this time with the vanilla list inductive type.
   The second version of these has the difference in the inductive case instead of in the base case. *)

Time Patch Proof old6_v1 new6 as patch6_v1. (* S *) (* 0 [no lifting] *)
Time Patch Proof old6_v2 new6 as patch6_v2. (* S *) (* 1 [lifting] *)

Time Patch Proof new6 old6_v1 as patch6_v1_rev. (* S *) (* 0 [no lifting, reversal] *)
Time Patch Proof new6 old6_v2 as patch6_v2_rev. (* S *) (* 1 [lifting, reversal] *)

(* Here's a case that is hard to abstract, despite the change being simple *)

Time Patch Proof old8_v1 new8 as patch8_v1. (* S *) (* 25 [lifting] *)

(* Variants of this proof, some of which will fail *)

Time Patch Proof old8_v2 new8 as patch8_v2. (* S *) (* 0 [no lifting] *)
Time Patch Proof old8_v3 new8 as patch8_v3. (* S *) (* 0 [no lifting] *)
Time Patch Proof old8_v4 new8 as patch8_v4. (* F *) (* 0 [no lifting] *)
Time Patch Proof old8_v5 new8 as patch8_v5. (* F *) (* 0 [no lifting] *)
Time Patch Proof old8_v6 new8 as patch8_v6. (* F *) (* 0 [no lifting] *)

(* Different rewrite vectors, difficulty unfolding constants and so on.
   Look at these terms to see what makes some of them harder than others.
   Note that when we fail, we fail fast. In the only case so far
   where we failed with many candidates, it was because we found
   a patch in one direction but couldn't invert it. *)

Definition new9 := new8.

(* These two are propositionally equal. *)

(* Here, v1 fails because we don't unwrap le_max_l and le_max_r.
   And we can't support patches between those two yet, also.

   v2 fails because of rewrite direction, much like in the other one.

   Abstraction is really hard for v3!

   applied patch is:
     eq_ind_r (fun n1 : nat => n <= n1) H0 (Nat.max_comm n n0)
   : n <= max n0 n -> (fun n1 : nat => n <= n1) (max n n0)

   And we want:
     eq_ind_r (fun n1 : nat => n <= n1) H0 (Nat.max_comm m n0)
   : n <= max n0 m -> (fun n1 : nat => n <= n1) (max m n0)

    So, we abstract by n, which we know to do because of
    the types of eq_ind_r. But in doing so, we also modify P,
    which we don't want to do. The key is that P has
    an n in it as well, and we don't want to touch that P.

    Can improve abstraction dramatically in this case by making it aware
    of properties. We should check if this works in other cases,
    too.
 *)

Time Patch Proof old9_v1 new9 as patch9_v1. (* F *) (* 0 [no lifting] *)
Time Patch Proof old9_v2 new9 as patch9_v2. (* F *) (* 0 [no lifting] *)
Time Patch Proof old9_v3 new9 as patch9_v3. (* S *) (* 97 [lifting] *)
Time Patch Proof old9_v4 new9 as patch9_v4. (* S *) (* 0 [no lifting] *)

Time Patch Proof new9 old9_v1 as patch9_v1_rev. (* F *) (* 0 [no lifting, reversal] *)
Time Patch Proof new9 old9_v2 as patch9_v2_rev. (* F *) (* 0 [no lifting, reversal] *)
Time Patch Proof new9 old9_v3 as patch9_v3_rev. (* S *) (* 97 [lifting, reversal] *)
Time Patch Proof new9 old9_v4 as patch9_v4_rev. (* S *) (* 0 [no lifting, reversal] *)

(* These are variants of two case study lemmas that are propositionally equal.
   These come from Induction.v.
   The variation here is moving the rewrite, but holding
   everything else exactly the same.

   V2 failing is because the arguments between old goal type
   and new goal type internally are inconsistent, so it doesn't
   know how to try to abstract. Right now it doesn't even bother
   trying.  *)

Time Patch Proof old10_v1 new10 as patch10_v1. (* S *) (* 0 *)
Time Patch Proof old10_v2 new10 as patch10_v2. (* F *) (* 0 *)

Time Patch Proof new10 old10_v1 as patch10_v1_rev. (* S *) (* 0 *)
Time Patch Proof new10 old10_v2 as patch10_v2_rev. (* F *) (* 0 *)

(*
 * Another one from the case studies
 * Note that you can show the same proof with or without passing
 * through a patch. So in one of these, a patch doesn't show up
 * in the difference, but in the other, it does.
 *)

Time Patch Proof old11_v1 new11 as patch11_v1. (* S *) (* 0 *)
Time Patch Proof old11_v2 new11 as patch11_v2. (* F *) (* 6 *)

Time Patch Proof new11 old11_v1 as patch11_v1_rev. (* S *) (* 0 *)
Time Patch Proof new11 old11_v2 as patch11_v2_rev. (* F *) (* 6 *)

(* 33 / 50 for reduction strategies *)
(* 31 / 50 for no reduction strategies *)
(* 33 / 50 for both (so the 2 that fail without reduction are interesting) *)


(* ... case with tree-like inductive type, TODO *)
(* Double-check answers before using this elsewhere *)

(* All 50 take less than a few seconds total to run. Slowest is .048 seconds *)


(* TODO run with no-reduce strategies too to see what happens *)
(* Also, take one that's hard and manually break it up and abstract those to see
   what happens, too; might be interesting *)

(* 17 fail, 33 succeed *)
