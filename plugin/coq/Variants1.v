(* Variants for first proof *)

Require Import Arith NPeano.

(*
   Things we can change:
   1. Outside/inside induction
   2. Apply to conclusion/apply to hypothesis/both
   3. Apply function/use hint or rewrite db/use special tactic
*)

(* Try all pairs of old and new, see what happens *)

Theorem new1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0; auto.
Qed.

(* Variant 1: Outside, conclusion, function *)

Theorem old1_v1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. apply le_plus_trans. induction H0; auto.
Qed.

(* Variant 2: Inside, conclusion, function *)

Theorem old1_v2:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - auto with arith.
  - constructor. auto.
Qed.

(* Variant 3: Outside, conclusion, rws [1] *)

Theorem old1_v3:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. rewrite le_plus_trans; auto. induction H0; auto.
Qed.

(* Variant 4: Inside, conclusion, rw [2] *)

Theorem old1_v4:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - rewrite le_plus_trans; auto.
  - constructor. auto.
Qed.

